/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Your Name <andrewid@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */
#define SMALL 64
#define MEDIUM 1024
#define LARGE 8192
/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.  Technically
 * it only works for EXPRs for which (0 && (EXPR)) is valid, but I
 * cannot think of any EXPR usable as a _function parameter_ that
 * doesn't qualify.
 *
 * The "diagnostic push/pop/ignored" pragmas are required to prevent
 * clang from issuing "unused value" warnings about most of the
 * arguments to dbg_printf / dbg_printheap (the argument list is being
 * treated, in this case, as a chain of uses of the comma operator).
 * Yes, these apparently GCC-specific pragmas work with clang,
 * I checked.
 *   -zw 2022-07-15
 */
#define dbg_discard_expr_(expr)                                                \
    (_Pragma("GCC diagnostic push") _Pragma(                                   \
        "GCC diagnostic ignored \"-Wunused-value\"")(void)(0 && (expr))        \
         _Pragma("GCC diagnostic pop"))
#define dbg_requires(expr) dbg_discard_expr_(expr)
#define dbg_assert(expr) dbg_discard_expr_(expr)
#define dbg_ensures(expr) dbg_discard_expr_(expr)
#define dbg_printf(...) dbg_discard_expr_((__VA_ARGS__))
#define dbg_printheap(...) dbg_discard_expr_((__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GNU compiler extension. This will
     * allow us to obtain a pointer to the start of the payload. (The similar
     * standard-C feature of "flexible array members" won't work here because
     * those are not allowed to be members of a union.)
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union {
        struct {
            struct block *prev;
            struct block *next;
        };
        char payload[0];
    };

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     */
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
static block_t *heap_end = NULL;

static block_t *small_root = NULL;
static block_t *small_tail = NULL;

static block_t *medium_root = NULL;
static block_t *medium_tail = NULL;

static block_t *large_root = NULL;
static block_t *large_tail = NULL;

static block_t *MAX_root = NULL;
static block_t *MAX_tail = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc);
}
/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/
static void remove_block(block_t *block) {
    if (block->prev == NULL && block->next == NULL) {
        if (block == small_root) {
            small_root = NULL;
            small_tail = NULL;
        }
        if (block == medium_root) {
            medium_root = NULL;
            medium_tail = NULL;
        }
        if (block == large_root) {
            large_root = NULL;
            large_tail = NULL;
        }
        if (block == MAX_root) {
            MAX_root = NULL;
            MAX_tail = NULL;
        }
    } else if (block->prev == NULL && block->next != NULL) {
        if (block == small_root) {
            small_root = block->next;
            block->next->prev = NULL;
        }
        if (block == medium_root) {
            medium_root = block->next;
            block->next->prev = NULL;
        }
        if (block == large_root) {
            large_root = block->next;
            block->next->prev = NULL;
        }
        if (block == MAX_root) {
            MAX_root = block->next;
            block->next->prev = NULL;
        }
    } else if (block->prev != NULL && block->next == NULL) {
        if (block == small_tail) {
            small_tail = block->prev;
            block->prev->next = NULL;
        }
        if (block == medium_tail) {
            medium_tail = block->prev;
            block->prev->next = NULL;
        }
        if (block == large_tail) {
            large_tail = block->prev;
            block->prev->next = NULL;
        }
        if (block == MAX_tail) {
            MAX_tail = block->prev;
            block->prev->next = NULL;
        }
    } else {
        block->prev->next = block->next;
        block->next->prev = block->prev;
    }
}

static block_t *insert(block_t *block) {
    size_t curr_size = get_size(block);
    if (curr_size < SMALL) {
        if (small_root == NULL) {
            small_root = block;
            small_tail = block;
            block->next = NULL;
            block->prev = NULL;
        } else {
            block->next = NULL;
            block->prev = small_tail;
            small_tail->next = block;
            small_tail = block;
        }
    } else if (SMALL <= curr_size && curr_size < MEDIUM) {
        if (medium_root == NULL) {
            medium_root = block;
            medium_tail = block;
            block->next = NULL;
            block->prev = NULL;
        } else {
            block->next = NULL;
            block->prev = medium_tail;
            medium_tail->next = block;
            medium_tail = block;
        }
    } else if (MEDIUM <= curr_size && curr_size < LARGE) {
        if (large_root == NULL) {
            large_root = block;
            large_tail = block;
            block->next = NULL;
            block->prev = NULL;
        } else {
            block->next = NULL;
            block->prev = large_tail;
            large_tail->next = block;
            large_tail = block;
        }
    } else {
        if (MAX_root == NULL) {
            MAX_root = block;
            MAX_tail = block;
            block->next = NULL;
            block->prev = NULL;
        } else {
            block->next = NULL;
            block->prev = MAX_tail;
            MAX_tail->next = block;
            MAX_tail = block;
        }
    }
    return block;
}
/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    bool is_next_alloc = get_alloc(find_next(block));
    bool is_prev_alloc;
    if (find_prev(block) == NULL) {
        is_prev_alloc = true;
    } else {
        is_prev_alloc = get_alloc(find_prev(block));
    }
    size_t size = get_size(block);
    // Case 1: Allocated blocks on both sides
    if (is_prev_alloc && is_next_alloc) {
        size_t curr_size = size;
        write_block(block, curr_size, false);
        insert(block);
        return block;
    }
    // Case 2: Free blocks on both sides
    else if (!is_prev_alloc && !is_next_alloc) {
        block_t *left = footer_to_header(find_prev_footer(block));
        block_t *right = find_next(block);
        size_t right_size = get_size(right);
        size_t left_size = get_size(left);
        remove_block(left);
        remove_block(right);
        write_block(left, left_size + right_size + size, false);
        insert(left);
        return left;

    }
    // Case 3: Free block on the left and allocated block on right
    else if (!is_prev_alloc && is_next_alloc) {
        block_t *left = footer_to_header(find_prev_footer(block));
        size_t left_size = get_size(left);
        remove_block(left);
        write_block(left, left_size + size, false);
        insert(left);
        return left;

    }
    // Case 4: Allocated block on the left and free block on right
    else {
        block_t *right = find_next(block);
        size_t right_size = get_size(right);
        write_block(block, right_size + size, false);
        remove_block(right);
        insert(block);
        return block;
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);
    heap_end = block_next;

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true);

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false);
        block_next->prev = NULL;
        block_next->next = NULL;
        coalesce_block(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;

    if (asize < SMALL) {
        if (small_root != NULL) {
            block = small_root;
            while (block != NULL) {
                if (get_size(block) >= asize) {
                    return block;
                }
                block = block->next;
            }
        }
        if (medium_root != NULL) {
            return medium_root;
        }
        if (large_root != NULL) {
            return large_root;
        }
        if (MAX_root != NULL) {
            return MAX_root;
        }
        return NULL;
    } else if (SMALL <= asize && asize < MEDIUM) {
        if (large_root != NULL) {
            return large_root;
        }
        if (MAX_root != NULL) {
            return MAX_root;
        }
        if (medium_root != NULL) {
            block = medium_root;
            while (block != NULL) {
                if (get_size(block) >= asize) {
                    return block;
                }
                block = block->next;
            }
        }
        return NULL;
    } else if (MEDIUM <= asize && asize < LARGE) {
        if (large_root != NULL) {
            block = large_root;
            while (block != NULL) {
                if (get_size(block) >= asize) {
                    return block;
                }
                block = block->next;
            }
        }
        if (MAX_root != NULL) {
            return MAX_root;
        }
        return NULL;
    } else {
        if (MAX_root != NULL) {
            block = MAX_root;
            while (block != NULL) {
                if (get_size(block) >= asize) {
                    return block;
                }
                block = block->next;
            }
        }
        return NULL;
    }
    return NULL; // no fit found
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    // Checks consistency of HEAP
    if (heap_start == NULL)
        return false;
    //  if(!(get_alloc(heap_start) && get_alloc(heap_end))) return false;
    // if(!(get_size(heap_start)==0 && get_size(heap_end)==0)) return false;
    word_t free_count = 0;
    block_t *block = heap_start;
    size_t total_allocated = 0;
    size_t heap_free = 0;
    size_t list_free = 0;
    while (block != heap_end) {
        if (block == NULL)
            return false;
        word_t header = block->header;
        word_t *footer = header_to_footer(block);
        size_t size = get_size(block);
        bool isAlloc = get_alloc(block);
        if ((((word_t)(block->payload)) & 0xF) != 0) {
            return false;
        }
        if (header != (*footer)) {
            return false;
        }
        if (size < min_block_size || size < 0) {
            return false;
        }
        if (!isAlloc) {
            if (!get_alloc(find_next(block))) {
                return false;
            }
            free_count++;
            heap_free += size;
        } else {
            total_allocated += size;
        }
        block = find_next(block);
    }
    word_t list_count = 0;

    block = small_root;
    while (block != NULL) {
        block_t *next_block = block->next;
        size_t size = get_size(block);
        if (next_block == NULL && block != small_tail) {
            return false;
        }
        if (next_block != NULL && next_block->prev != block) {
            return false;
        }
        if (!(size < SMALL)) {
            return false;
        }
        list_count++;
        list_free += size;
        block = block->next;
    }

    block = medium_root;
    while (block != NULL) {
        block_t *next_block = block->next;
        size_t size = get_size(block);
        if (next_block == NULL && block != medium_tail) {
            return false;
        }
        if (next_block != NULL && next_block->prev != block) {
            return false;
        }
        if (!(SMALL <= size && size < MEDIUM)) {
            return false;
        }
        list_count++;
        list_free += size;
        block = block->next;
    }

    block = large_root;
    while (block != NULL) {
        block_t *next_block = block->next;
        size_t size = get_size(block);
        if (next_block == NULL && block != large_tail) {
            return false;
        }
        if (next_block != NULL && next_block->prev != block) {
            return false;
        }
        if (!(MEDIUM <= size && size < LARGE)) {
            return false;
        }
        list_count++;
        list_free += size;
        block = block->next;
    }
    block = MAX_root;
    while (block != NULL) {
        block_t *next_block = block->next;
        size_t size = get_size(block);
        if (next_block == NULL && block != MAX_tail) {
            return false;
        }
        if (next_block != NULL && next_block->prev != block) {
            return false;
        }
        if (!(LARGE <= size)) {
            return false;
        }
        list_count++;
        list_free += size;
        block = block->next;
    }
    // printf("list free total is: %lu, list count total is: %lu \n", list_free,
    // list_count); printf("heap free total is: %lu, heap count total is: %lu
    // \n", heap_free, free_count);
    printf("total allocated: %lu \n", total_allocated);
    if (list_count != free_count || list_free != heap_free) {
        printf("not match");
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    small_root = NULL;
    small_tail = NULL;
    medium_root = NULL;
    medium_tail = NULL;
    large_root = NULL;
    large_tail = NULL;
    MAX_root = NULL;
    MAX_tail = NULL;

    if (start == (void *)-1) {
        return false;
    }
    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    heap_end = heap_start;

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */

void *malloc(size_t size) {
    //  dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    remove_block(block);
    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    //  dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);
    // Try to coalesce the block with its neighbors
    coalesce_block(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/**
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
