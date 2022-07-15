/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * Malloc package, when the user asks for a certain size of block in memory,
 *this program will facilitate that, including the freeing of blocks at the end.
 * This program uses a better fit search, along with segregated lists
 * and footerless and mini-block implementation to optimize the throughput and
 * utilization rate of the memory. The inherent representation is the "block",
 * where each block has a header and possibly a footer, and the data payload,
 * the user is only able to see and work with the data payload section of the
 * block but the header and footer are necessary for the program to ensure
 *correctness of malloc and free operations. Mini blocks are put into a separate
 *linked list to allow better utilization performances, there are 14 bucket
 *lists in the segregated lists, with the smallest bucket list having range (16,
 *32] and each subsequence list has range increased by a factor of 2.
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
 * @author Haocheng Yang hryang@andrew.cmu.edu
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

/** @brief Determines how many blocks with size at least asize that we will
 *look at in find_fit
 */
#define LIMIT 5
/** @brief number of lists in the segregated list
 */
#define SIZE 14

/** @brief the smallest size bucket for the segregated list
 */
#define BASE 16
/**
The alignment requirement for payload in the heap, which is 16 bytes
*/
#define ALIGN 0xF
/**
Constant used for pointer arithmetic
*/
#define WORD_SHIFT 7
/**
Largest unsigned long
*/
#define UMAX 0xFFFFFFFFFFFFFFFF
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
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * chunk size is the minimum size that the heap is
 * increased by each time it is extended and
 * is the size of the initial heap. Currently
 * is 4096
 */
static const size_t chunksize = (1 << 12);

/**
 * @brief: this is the first bit in a word,
 * this bit is used to keep track whether the
 * block is allocated or not. This bit will not
 * be contaminated by the size of the header since
 * the size must be a multiple of 16
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief: this is the second bit in a word,
 * this bit is used to keep track whether the previous
 * block is allocated or not. This bit will not
 * be contaminated by the size of the header since
 * the size must be a multiple of 16
 */

static const word_t prev_alloc_mask = 0x2;

/**
 * @brief: this is the third bit in a word,
 * this bit is used to keep track whether the previous
 * block is a mini-block or not. This bit will not
 * be contaminated by the size of the header since
 * the size must be a multiple of 16
 */

static const word_t prev_mini_mask = 0x4;

/**
 * @brief the size mask it the first 60 bits in a word (long)
 * all set to 1, this is to get the size information in the header of the block,
 * since the size must be a mutliple of 16, that means the last 4 bits will be 0
 * anyway so we don't have to check for that.
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
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
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };

} block_t;

typedef struct list {
    block_t *root;
} list_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;
/**@brief array of the bucket list, segregated list*/
static list_t root[SIZE];
/**@brief mini block list */
static block_t *tiny_root = NULL;
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
static bool check_prev(block_t *block) {
    if (((block->header) & prev_alloc_mask)) {
        return true;
    } else {
        return false;
    }
}

/**
 * @brief
 *
 * Checks whether or not the previous block of the
 * input is a mini-block or not.
 *
 *
 * @param[in] block to be checked
 * @return true if the previous block is a mini-block,
 * false otherwise
 */
static bool check_prev_mini(block_t *block) {
    if ((block->header) & prev_mini_mask) {
        return true;
    } else {
        return false;
    }
}

/**
 * @brief function that when given a size, it will calculate the
 * bucket list that it belongs to, returned as an index in the
 * array of bucket lists. Note that the bucket list sizes is
 * multiplied by 2 each time, with the first bucket list being
 * in the range (16, 32]
 *
 * @param[in] size
 * @return the bucket list input size would belong to
 * @pre size > 0
 */
static size_t find_index(size_t size) {
    size_t base = BASE;
    size_t counter = 0;
    for (; counter < SIZE; counter++) {
        if (base >= size) {
            return counter;
        }
        base = base << 1;
    }
    if (counter == SIZE) {
        return SIZE - 1;
    }
    return counter;
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
    return asize - wsize;
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
 * @brief sets the prev_alloc bit of the header, it will
 * also set the footer if it exists (free non-mini block)
 *
 * @param[in] block, the block to be set
 * @param[in] prev_alloc, whether or not the previous block is a
 * allocated
 */
static void set_prev_alloc(block_t *block, bool prev_alloc) {
    if (prev_alloc) {
        block->header = (block->header) | prev_alloc_mask;
    } else {
        block->header = (block->header) & (~(prev_alloc_mask));
    }
    if (!get_alloc(block) && get_size(block) > min_block_size) {
        word_t *footer = header_to_footer(block);
        if (prev_alloc) {
            *footer = (*footer) | prev_alloc_mask;
        } else {
            *footer = (*footer) & (~(prev_alloc_mask));
        }
    }
}
/**
 * @brief sets the prev_mini_block bit of the header, it will
 * also set the footer if it exists (free non-mini block)
 *
 * @param[in] block, the block to be set
 * @param[in] prev_mini, whether or not the previous block is a
 * mini-block
 */
static void set_prev_mini(block_t *block, bool prev_mini) {
    if (prev_mini) {
        block->header = (block->header) | prev_mini_mask;
    } else {
        block->header = (block->header) & (~(prev_mini_mask));
    }
    if (!get_alloc(block) && get_size(block) > min_block_size) {
        word_t *footer = header_to_footer(block);
        if (prev_mini) {
            *footer = (*footer) | prev_mini_mask;
        } else {
            *footer = (*footer) & (~(prev_mini_mask));
        }
    }
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes a header, and the footer is only
 * written if the block is a free non-mini block
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] is_prev_alloc whether or not the preivous block is allocated
 * @param[in] is_prev_mini whether or not the previous block is a mini-block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool is_prev_alloc, bool is_prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc);
    if (is_prev_alloc)
        block->header = block->header | prev_alloc_mask;
    else
        block->header = block->header & (~(prev_alloc_mask));
    if (is_prev_mini)
        block->header = block->header | prev_mini_mask;
    else
        block->header = block->header & (~(prev_mini_mask));
    if (!alloc && (size > min_block_size)) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc);
        if (is_prev_alloc)
            *footerp = *footerp | prev_alloc_mask;
        else
            *footerp = *footerp & (~(prev_alloc_mask));
        if (is_prev_mini)
            *footerp = *footerp | prev_mini_mask;
        else
            *footerp = *footerp & (~(prev_mini_mask));
    }
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

/**
 * @brief Loops through the entire mini-block list to
 * find the previous block of the input block since prev
 * does not exist for mini-blocks
 *
 * @param[in] mini -lock
 * @return mini-block that is the previous of the input
 * block inside the mini-block list
 * @pre the block must be a mini-block
 */
static block_t *mini_prev(block_t *block) {
    block_t *curr = tiny_root;
    while (curr != NULL) {
        if (curr->next == block) {
            return curr;
        }
        curr = curr->next;
    }
    return NULL;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/
/**
 * @brief This function takes in a free block that is
 * either on the the mini-block list or one of the other
 * bucket lists. It logically removes the block from its
 * corresponding list.
 *
 * @param[in] block, block to be removed
 * @return
 * @pre the block must be free
 *
 *
 */
static void remove_block(block_t *block) {
    size_t size = get_size(block);
    if (size <= min_block_size) {
        block_t *prev = mini_prev(block);
        if (prev == NULL && block->next == NULL) {
            if (block == tiny_root) {
                tiny_root = NULL;
            }
        } else if (prev == NULL && block->next != NULL) {
            tiny_root = block->next;
        } else if (prev != NULL && block->next == NULL) {
            prev->next = NULL;
        } else {
            prev->next = block->next;
        }
    } else {
        size_t index = find_index(get_size(block));
        if (block->prev == NULL && block->next == NULL) {
            if (block == root[index].root) {
                root[index].root = NULL;
            }
        } else if (block->prev == NULL && block->next != NULL) {
            if (block == root[index].root) {
                block->next->prev = NULL;
                root[index].root = block->next;
            }
        } else if (block->prev != NULL && block->next == NULL) {
            block->prev->next = NULL;
        } else {
            block->prev->next = block->next;
            block->next->prev = block->prev;
        }
    }
}
/**
 * @brief This function takes in a free block and adds
 * it to either the mini-block list or one of the bucket
 * lists depending on its size. It is implemented in a FIFO
 * structure
 *
 * @param[in] block to be inserted
 * @return
 * @pre block must be free
 *
 */

static void insert(block_t *block) {
    size_t size = get_size(block);
    if (size <= min_block_size) {
        block->next = tiny_root;
        tiny_root = block;
    } else {
        size_t index = find_index(get_size(block));
        if (root[index].root == NULL) {
            root[index].root = block;
            block->next = NULL;
            block->prev = NULL;
        } else {
            block->next = root[index].root;
            root[index].root->prev = block;
            block->prev = NULL;
            root[index].root = block;
        }
    }
}

/**
 * @brief
 * This function takes in a free block and checks if
 * there are possibilities of joining the free block
 * with its neighboring blocks. It returns a pointer to
 * the newly joined free block if it is possible or returns
 * the free block itself if there are no coalescing
 *
 *
 * @param[in] block to be coalesced
 * @return pointer to the coalesced result of the block
 * with its neighbors
 * @pre block must be free
 */
static block_t *coalesce_block(block_t *block) {
    bool is_next_alloc = get_alloc(find_next(block));
    bool is_prev_alloc = check_prev(block);
    size_t size = get_size(block);

    // Case 1: Allocated blocks on both sides
    if (is_prev_alloc && is_next_alloc) {
        bool is_prev_mini = check_prev_mini(block);
        size_t curr_size = size;
        write_block(block, curr_size, false, true, is_prev_mini);
        block_t *next_block = find_next(block);
        set_prev_alloc(next_block, false);
        if (curr_size <= min_block_size)
            set_prev_mini(next_block, true);
        else
            set_prev_mini(next_block, false);
        insert(block);
        return block;
    }

    // Case 2: Free blocks on both sides
    else if (!is_prev_alloc && !is_next_alloc) {
        block_t *left;
        bool is_prev_mini = check_prev_mini(block);
        if (is_prev_mini)
            left = (block_t *)(&(block->header) - 2);
        else
            left = footer_to_header(find_prev_footer(block));
        block_t *right = find_next(block);
        size_t right_size = get_size(right);
        size_t left_size = get_size(left);
        bool left_mini = check_prev_mini(left);
        remove_block(left);
        remove_block(right);
        write_block(left, left_size + right_size + size, false, true,
                    left_mini);
        block_t *next_block = find_next(left);
        set_prev_alloc(next_block, false);
        set_prev_mini(next_block, false);
        insert(left);
        return left;

    }

    // Case 3: Free block on the left and allocated block on right
    else if (!is_prev_alloc && is_next_alloc) {
        block_t *left;
        bool is_prev_mini = check_prev_mini(block);
        if (is_prev_mini)
            left = (block_t *)(&(block->header) - 2);
        else
            left = footer_to_header(find_prev_footer(block));
        size_t left_size = get_size(left);
        bool left_mini = check_prev_mini(left);
        remove_block(left);
        write_block(left, left_size + size, false, true, left_mini);
        block_t *next_block = find_next(left);
        set_prev_alloc(next_block, false);
        set_prev_mini(next_block, false);
        insert(left);
        return left;

    }

    // Case 4: Allocated block on the left and free block on right
    else {
        block_t *right = find_next(block);
        size_t right_size = get_size(right);
        //  bool is_alloc = check_prev(block);
        bool is_mini = check_prev_mini(block);
        //  assert(is_alloc);
        remove_block(right);
        write_block(block, right_size + size, false, true, is_mini);
        block_t *next_block = find_next(block);
        set_prev_alloc(next_block, false);
        set_prev_mini(next_block, false);
        //  assert(get_size(block) > min_block_size);
        assert(get_alloc(next_block));
        insert(block);
        return block;
    }
}

/**
 * @brief
 *
 * Extends the heap by size specified. Note that the input size must
 * be a positive integer that is at least chunk_size to ensure we don't
 * repeatedly extend the heap too many times.
 * The function will extend the heap and move the epilogue
 * as needed, in addition it will coalesce any blocks if necessary and
 * returns a pointer to the last valid block in the new heap
 *
 * @param[in] size must be at least chunk size
 * @return pointer to last valid block in extended heap
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    word_t *heap_end = (word_t *)(((char *)mem_heap_hi()) - WORD_SHIFT);
    bool is_last_alloc = (*heap_end) & prev_alloc_mask;
    bool is_last_mini = (*heap_end) & prev_mini_mask;
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, is_last_alloc, is_last_mini);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);
    set_prev_alloc(block_next, false);
    set_prev_mini(block_next, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    return block;
}

/**
 * @brief
 * The input must be an allocated block and a positive size,
 * if the block can be partitioned into two blocks,
 * one with same size as input and the other half must be
 * at least the size of min_block_size, the function will
 * partition the block where the block with desired size is
 * still allocated but the other half is now free. This is to
 * save space for future malloc calls. If the block cannot be
 * partitioned that way, then the function will do nothing.
 * @param[in] block to be split
 * @param[in] asize
 * @pre block must be allocated
 */

static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));

    size_t block_size = get_size(block);
    bool prev_alloc = check_prev(block);
    bool prev_mini = check_prev_mini(block);
    bool first_mini = false;
    bool second_mini = false;
    if (asize <= min_block_size) {
        first_mini = true;
    }
    if ((block_size - asize) <= min_block_size && (block_size - asize >= 0)) {
        second_mini = true;
    }

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, prev_alloc, prev_mini);
        block_next = find_next(block);

        write_block(block_next, block_size - asize, false, true, first_mini);

        block_t *next_next = find_next(block_next);
        set_prev_alloc(next_next, false);
        set_prev_mini(next_next, second_mini);
        if (second_mini) {
            block_next->next = NULL;
        } else {
            block_next->next = NULL;
            block_next->prev = NULL;
        }
        coalesce_block(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * This is a helper function that given a size, it  will
 * find the free block in the segregated list whose size is
 * at least the input. It first looks at the bucket list
 * where the size belongs to. Then it will look from the
 * start of the list and finds at most 5 blocks that is
 * at least the size of input, it will then take the block
 * the best fits the size and returns it. If such a block does
 * not exist then it will just take the first block in the bucket list
 * whose size is one step above the current one. If no such blocks exists,
 * it will return NULL
 *
 * @param[in] asize
 * @return free block whose size is at least asize or NULL if non-exists
 * @pre asize > 0
 */

static block_t *find_fit_helper(size_t asize) {
    size_t index = find_index(asize);
    block_t *block = root[index].root;
    block_t *fit = NULL;
    size_t diff = UMAX;
    size_t counter = 0;
    while (block != NULL && counter <= LIMIT) {
        if (get_size(block) >= asize) {
            if (get_size(block) - asize < diff) {
                fit = block;
                diff = get_size(block) - asize;
            }
            counter++;
        }
        block = block->next;
    }
    index++;
    if (fit == NULL) {
        for (size_t i = index; i < SIZE; i++) {
            if (root[i].root != NULL) {
                return root[i].root;
            }
        }
        return NULL;
    } else {
        return fit;
    }
}
/**
 * @brief
 *
 * Function that finds the free block whose size is
 * at least asize. If asize is <= 16 bytes, then it will look in
 * the mini-blocks, if none is found or if size is greater than
 * 16 bytes, it will call find_helper as described above.
 *
 * @param[in] asize, the desired size
 * @return free block whose size is at least asize,
 * NULL if non found
 * @pre asize > 0
 */

static block_t *find_fit(size_t asize) {
    if (asize <= min_block_size) {
        if (tiny_root != NULL) {
            return tiny_root;
        } else {
            return find_fit_helper(asize);
        }
    } else {
        return find_fit_helper(asize);
    }
}
/**
 * @brief
 *
 * Checks the heap invariant everytime the heap is updated
 * returns true if all invariants are satisifed and false
 * if any invariants have been violated
 *
 * @return
 */

bool mm_checkheap(int line) {

    word_t *prologue_ptr = (word_t *)mem_heap_lo();
    bool prologue_alloc = extract_alloc(*prologue_ptr);
    size_t prologue_size = extract_size(*prologue_ptr);
    word_t *heap_end = (word_t *)(((char *)mem_heap_hi()) - WORD_SHIFT);
    bool epilogue_alloc = extract_alloc(*heap_end);
    size_t epilogue_size = extract_size(*heap_end);
    if (!(prologue_alloc && prologue_size == 0)) {
        return false;
    }
    if (!(epilogue_alloc && epilogue_size == 0)) {
        return false;
    }

    block_t *block = heap_start;
    while ((word_t)block != (word_t)heap_end) {
        size_t size = get_size(block);
        word_t header = block->header;

        if (((word_t)(block->payload) & ALIGN) != 0) {
            return false;
        }
        if ((word_t)block < (word_t)heap_start) {
            return false;
        }
        char *last_byte = ((char *)header_to_footer(block)) + WORD_SHIFT;
        if ((word_t)last_byte >= (word_t)heap_end) {
            return false;
        }
        if (size < min_block_size) {

            return false;
        }
        if ((word_t)find_next(block) != (word_t)heap_end) {
            if (!get_alloc(block) && !get_alloc(find_next(block))) {
                return false;
            }
        }
        if (!get_alloc(block) && get_size(block) > min_block_size) {
            word_t footer = *(header_to_footer(block));
            if (footer != header) {
                return false;
            }
        }
        block = find_next(block);
    }
    for (size_t i = 0; i < SIZE; i++) {
        block = root[i].root;
        while (block != NULL) {
            size_t size = get_size(block);
            if (block->next != NULL) {
                if (block->next->prev != block) {
                    return false;
                }
            }
            if ((word_t)block < (word_t)heap_start) {
                return false;
            }
            char *last_byte = ((char *)header_to_footer(block)) + WORD_SHIFT;
            if ((word_t)last_byte >= (word_t)heap_end) {
                return false;
            }
            size_t index = find_index(size);
            if (index != i) {
                return false;
            }
            block = block->next;
        }
    }
    return true;
}

/**
 * @brief
 *
 * Initializes the heap including the prologue and
 * epilgue blocks. It then initializes some global variables
 * such as heap_start and each of the roots of the bucket lists.
 * The initialized heap has size chunksize
 *
 * @return true if initailization success, false otherwise
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));
    for (int i = 0; i < SIZE; i++) {
        root[i].root = NULL;
    }
    tiny_root = NULL;
    if (start == (void *)-1) {
        return false;
    }
    start[0] = pack(0, true); // Heap prologue (block footer)
    start[1] = pack(0, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);
    set_prev_alloc(heap_start, true);
    set_prev_mini(heap_start, false);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * Given a size, the function will return a pointer
 * to a block whose size is at least the input and the
 * block can be freely used by the user. It will return NULL
 * if no such block in memory exists.
 *
 * @param[in] size
 * @return pointer to block whose size is at least size, returns
 * NULL if none found.
 * @pre size >=0
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

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
    asize = round_up(size + wsize, dsize);
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

    bool prev_alloc = check_prev(block);
    bool prev_mini = check_prev_mini(block);
    remove_block(block);
    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true, prev_alloc, prev_mini);
    // Try to split the block if too large
    block_t *next = find_next(block);
    set_prev_alloc(next, true);
    if (block_size <= min_block_size) {
        set_prev_mini(next, true);
    } else {
        set_prev_mini(next, false);
    }
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * Given an allocated block, the function
 * will logically free it and put it into
 * the segregated list and the memory is given
 * back to the system
 *
 * @param[in] bp, pointer to allocated block
 * @pre bp must point to an allocated block
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }
    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);
    bool prev_alloc = check_prev(block);
    bool prev_mini = check_prev_mini(block);
    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, prev_alloc, prev_mini);
    block_t *next_block = find_next(block);
    set_prev_alloc(next_block, false);
    if (size <= min_block_size)
        set_prev_mini(next_block, true);
    else
        set_prev_mini(next_block, false);
    // Try to coalesce the block with its neighbors
    coalesce_block(block);
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * This function will reallocate a block to a newsize,
 * by first freeing the original block and malloc another
 * block of the new size. If impossible, it will return NULL
 * and the original block will be intact.
 *
 * @param[in] ptr
 * @param[in] size
 * @return block whose size is at least input, frees the old block,
 * NULL if not possible and the original block is intact
 * @pre ptr must be a valid allocated block and size >= 0
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
 * Malloc but all data is initialized to 0
 *
 * @param[in] elements
 * @param[in] size
 * @return pointer to block of at least size and
 * everythign inside the block is initialized to 0
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
