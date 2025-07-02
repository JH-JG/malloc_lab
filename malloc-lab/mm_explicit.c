/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Krafton Jungle",
    /* First member's full name */
    "Lee JuHyung",
    /* First member's email address */
    "aaa",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Basic constants and macros
#define WSIZE               4
#define DSIZE               8
#define MIN_BLK_SIZE        16
#define CHUNKSIZE           (1 << 12)

# define MAX(x, y)          ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))

#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_PRED(bp)        (*(char **)(bp))
#define GET_SUCC(bp)        (*(char **)(bp + WSIZE))

#define SET_PRED(bp, val)   (*(char **)(bp) = val)
#define SET_SUCC(bp, val)   (*(char **)(bp + WSIZE) = val)


static char *heap_listp = 0; // 시작 블록
static char *free_listp = 0; // free된 블록만 연결

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_free_list(void *bp);
static void remove_from_free_list(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /*Create the initail empty heap*/
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0); // 시작점은 0
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1)); // Prologue Header 할당된 블럭의 크기는 16
    PUT(heap_listp + (2*WSIZE), 0); // Predecessor
    PUT(heap_listp + (3*WSIZE), 0); // Successor
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1)); // Prologue Footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); // Epliogue Block

    free_listp = heap_listp + (2 * WSIZE); // heap_listp + 8이 payload 위치가 됨
    heap_listp += (4 * WSIZE);

    SET_PRED(free_listp, free_listp);
    SET_SUCC(free_listp, free_listp);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    // 블록사이즈 조정
    if (size <=DSIZE){
        asize = 2 * DSIZE;
    }
    else {
        asize = DSIZE * ((size + (DSIZE + (DSIZE - 1))) / DSIZE); // 8의 배수를 만족시키기 위해
    }

    // 빈 공간에서 적절한 공간이 있다면 할당
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // 맞는 공간이 없다면
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    
    add_free_list(bp);
    place(bp, asize);

    return bp;
}

static void *find_fit(size_t asize){

    char *bp = GET_SUCC(free_listp);
    // first_fit
    while (bp != free_listp){
        if (asize <= GET_SIZE(HDRP(bp))) return bp;
        bp = GET_SUCC(bp);
    }

    return NULL;
}

static void place(void *bp, size_t asize){
    size_t total = GET_SIZE(HDRP(bp));

    if ((total - asize)>= (2*DSIZE)){
        remove_from_free_list(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1)); // 새로운 footer
        bp = NEXT_BLKP(bp); // 새로운 block pointer

        PUT(HDRP(bp), PACK(total - asize, 0)); //새로운 header
        PUT(FTRP(bp), PACK(total - asize, 0)); // 새로운 footer
        add_free_list(bp);
    }
    else{
        remove_from_free_list(bp);
        PUT(HDRP(bp), PACK(total, 1)); // 16바이트 이하라면 모두 할당
        PUT(FTRP(bp), PACK(total, 1));
    }

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    ptr = coalesce(ptr);

    add_free_list(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t original_size = GET_SIZE(HDRP(ptr));
    size_t aligned_size = ALIGN(size + DSIZE);

    if (original_size == aligned_size){
        return oldptr;
    }
    if (original_size > aligned_size && (original_size - aligned_size) >= MIN_BLK_SIZE){
        // 헤더 + 페이로드 + 푸터 = 최소사이즈 16
        PUT(HDRP(oldptr), PACK(aligned_size, 1));
        PUT(FTRP(oldptr), PACK(aligned_size, 1));
        newptr = NEXT_BLKP(oldptr);

        PUT(HDRP(newptr), PACK(original_size - aligned_size, 0));
        PUT(FTRP(newptr), PACK(original_size - aligned_size, 0));
        add_free_list(newptr);

        return oldptr;
    }
    else{
        newptr = mm_malloc(size);
        if (newptr == NULL)
            return NULL;
        copySize = original_size - DSIZE;
        if (size < copySize)
            copySize = size;
        memcpy(newptr, oldptr, copySize);
        mm_free(oldptr);
        return newptr;
    }
}

static void * extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp){

    // free_list를 병합/삭제 관리 로직 추가
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        remove_from_free_list(NEXT_BLKP(bp));
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void add_free_list(void *bp){
    // 빈 블록을 free_listp 앞에 삽입
    /*
    pred, succ 생성
    현재 free_listp의 주소를 가져오고
    그 앞에 삽입한다 포인터를 업데이트
    */
    void *free_ptr = GET_SUCC(free_listp); // free_listp는 기준점, 기준점 뒤로 삽입할 예정

    SET_PRED(bp, free_listp); // 앞(기준점) pred 가리킴
    SET_SUCC(bp, free_ptr);
    SET_PRED(free_ptr, bp);
    SET_SUCC(free_listp, bp);
}

static void remove_from_free_list(void *bp){
    if (GET_PRED(bp) == 0) return;
    void *prev_block = GET_PRED(bp);
    void *next_block = GET_SUCC(bp);

    SET_SUCC(prev_block, next_block);
    SET_PRED(next_block, prev_block);
    
}