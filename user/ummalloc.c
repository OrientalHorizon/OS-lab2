#include "kernel/types.h"

//
#include "user/user.h"

//
#include "ummalloc.h"

#include <stdalign.h>
#include <stddef.h>
// #include <string.h>

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(uint)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (* (unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *) (bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define TRUE 1  // 被分配
#define FALSE 0 // 未被分配

/*
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;

static void *coalesce(void *bp) {
  // 不用考虑边界条件（这是第一个块 / 最后一个块），之前在前后插空块已经解决掉了
  // if (GET_ALLOC(HDRP(bp)) == TRUE) return bp;

  char *prev_footer = FTRP(PREV_BLKP(bp));
  char *next_header = HDRP(NEXT_BLKP(bp));

  uint prev_alloc = GET_ALLOC(prev_footer);
  uint next_alloc = GET_ALLOC(next_header);

  if (prev_alloc == FALSE && next_alloc == FALSE) {
    // 一起合并
    // bug: GET_SIZE(bp) 不行！！！！必须是 GET_SIZE(HDRP(bp))
    uint size = GET_SIZE(HDRP(bp)) + GET_SIZE(prev_footer) + GET_SIZE(next_header);
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, FALSE));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FALSE));

    bp = PREV_BLKP(bp);
  }
  else if (prev_alloc == FALSE && next_alloc == TRUE) {
    // 跟前面合并
    uint size = GET_SIZE(HDRP(bp)) + GET_SIZE(prev_footer);
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, FALSE));
    PUT(FTRP(bp), PACK(size, FALSE));
    
    bp = PREV_BLKP(bp);
  }
  else if (prev_alloc == TRUE && next_alloc == FALSE) {
    uint size = GET_SIZE(HDRP(bp)) + GET_SIZE(next_header);
    PUT(HDRP(bp), PACK(size, FALSE));
    // PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FALSE));
    PUT(FTRP(bp), PACK(size, FALSE));
    // bug: 这里 bp 的 SIZE 已经改过了，不能再取 NEXT_BLKP 了！！！！

    // No need to modify bp
  }
  return bp;
}
static void *extend_heap(uint words) {
  char *bp;
  uint size = (words & 1) ? (words + 1) : words;
  size *= WSIZE;
  if ((long int)(bp = sbrk(size)) == -1) return NULL;
  // 这里别忘记 *4

  PUT(HDRP(bp), PACK(size, FALSE));
  PUT(FTRP(bp), PACK(size, FALSE));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, TRUE));

  return coalesce(bp);
}
int mm_init(void) {
  if ((heap_listp = sbrk(4 * WSIZE)) == (void *)-1) return -1;
  PUT(heap_listp, 0); // 对齐
  PUT(heap_listp + WSIZE, PACK(DSIZE, TRUE));
  PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, TRUE));
  PUT(heap_listp + 3 * WSIZE, PACK(0, TRUE)); // 结尾段
  heap_listp += 2 * WSIZE;

  if (!extend_heap(CHUNKSIZE / WSIZE)) return -1;
  return 0;
}

static void *find_fit(uint asize) {
  // 首次适配搜索
  uint block_size;
  for (char *bp = heap_listp; (block_size = GET_SIZE(HDRP(bp))) != 0; bp = NEXT_BLKP(bp)) {
    if (GET_ALLOC(HDRP(bp)) == FALSE && block_size >= asize) {
      return bp;
    }
  }
  return NULL;
}

static void place(void *bp, uint asize) {
  // 能分配，看块大小决定是否要拆
  uint block_size = GET_SIZE(HDRP(bp));
  if (block_size >= asize + 16) { // 暂定 16：头尾 + 8 bytes 对齐
  // 离谱，刚才忘记加 asize 了
    // 拆
    uint new_size = block_size - asize; // 不用再减，头尾标记算进块大小
    
    PUT(HDRP(bp), PACK(asize, TRUE));
    PUT(FTRP(bp), PACK(asize, TRUE));

    char *next_bp = NEXT_BLKP(bp);
    PUT(HDRP(next_bp), PACK(new_size, FALSE));
    PUT(FTRP(next_bp), PACK(new_size, FALSE));
  }
  else {
    // 不拆，直接返回
    PUT(HDRP(bp), PACK(block_size, TRUE));
    PUT(FTRP(bp), PACK(block_size, TRUE));
  }
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(uint size) {
  if (size == 0) return NULL;
  uint asize = (size <= DSIZE) ? DSIZE*2 : ALIGN(size);
  char *bp;
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  uint extend_size = MAX(CHUNKSIZE, asize);
  bp = extend_heap(extend_size / WSIZE);
  if (bp == NULL) return NULL;
  place(bp, asize);
  return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
  uint size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(size, FALSE)); // header
  PUT(FTRP(ptr), PACK(size, FALSE)); // footer
  coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, uint size) {
  // TODO
  if (ptr == NULL) return mm_malloc(size);
  if (size == 0) {
    free(ptr);
    return 0;
  }

  // uint asize = (size <= DSIZE) ? 16 : ALIGN(size + WSIZE * 2);
  void *oldptr = ptr;
  uint cur_size = GET_SIZE(HDRP(oldptr));
  // if (cur_size >= asize) {
  //   // shrink
  //   if (cur_size - asize >= 16) {
  //     PUT(HDRP(oldptr), PACK(asize, TRUE));
  //     PUT(FTRP(oldptr), PACK(asize, TRUE));

  //     char *newptr = NEXT_BLKP(oldptr);
  //     PUT(HDRP(newptr), PACK(cur_size - asize, FALSE));
  //     PUT(FTRP(newptr), PACK(cur_size - asize, FALSE));
  //     coalesce(newptr);
  //   }
  //   return oldptr;
  // }
  // else {
    // get some new space
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    uint new_size = GET_SIZE(HDRP(newptr));
    if (cur_size < new_size) {
      new_size = size;
    }
    memcpy(newptr, oldptr, new_size - WSIZE);
    mm_free(oldptr);
    return newptr;
  // }
}
