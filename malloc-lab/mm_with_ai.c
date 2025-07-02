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
#include <stdint.h>

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
# define MIN(x, y)          ((x) < (y) ? (x) : (y))

#define PACK(size, alloc, prev_alloc) ((size) | (alloc) | ((prev_alloc) << 1))

// 새로운 매크로들 추가
#define GET_PREV_ALLOC(p)   ((GET(p) & 0x2) >> 1)
#define SET_PREV_ALLOC(p)   (GET(p) | 0x2)
#define CLEAR_PREV_ALLOC(p) (GET(p) & ~0x2)

#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)


#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       (GET_PREV_ALLOC(HDRP(bp)) ? \
                            ((char *)(bp) - GET_PREV_SIZE(HDRP(bp))) : \
                            ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))))

// 이전 블록 크기를 저장하기 위한 매크로 (할당된 블록용)
#define GET_PREV_SIZE(p)    (GET((char *)(p) - WSIZE))
#define SET_PREV_SIZE(p, size) (PUT((char *)(p) - WSIZE, size))

#define GET_PRED(bp)        (*(char **)(bp))
#define GET_SUCC(bp)        (*(char **)(bp + WSIZE))

#define SET_PRED(bp, val)   (*(char **)(bp) = val)
#define SET_SUCC(bp, val)   (*(char **)(bp + WSIZE) = val)

// Reallocation 최적화를 위한 버퍼 크기
#define REALLOC_BUFFER 128



static char *heap_listp = 0; // 시작 블록
static char *seg_free_lists[12]; // segregated free lists 배열


static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_free_list(void *bp, size_t asize);
static void remove_from_free_list(void *bp);
static int select_list(size_t asize);
static size_t get_adaptive_chunksize(size_t asize);
static void update_next_prev_alloc(void *bp, int alloc);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // segregated free lists 초기화
    for (int i = 0; i < 12; i++) {
        seg_free_lists[i] = NULL;
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1, 1));
    PUT(heap_listp + (2*WSIZE), PACK(2*DSIZE, 1, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1));

    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}


static int select_list(size_t asize){
    if (asize <= 16) return 0;
    if (asize <= 32) return 1;
    if (asize <= 64) return 2;
    if (asize <= 128) return 3;
    if (asize <= 256) return 4;
    if (asize <= 512) return 5;
    if (asize <= 1024) return 6;
    if (asize <= 2048) return 7;
    if (asize <= 4096) return 8;
    if (asize <= 8192) return 9;
    if (asize <= 16384) return 10;
    return 11;
}

static size_t get_adaptive_chunksize(size_t asize) {
    if (asize <= 32) return asize * 5;
    if (asize <= 64) return asize * 4;
    if (asize <= 128) return asize * 3;
    if (asize <= 256) return asize * 2;
    return MAX(asize, CHUNKSIZE);
}

/// 2의 제곱수로 올림 함수
static size_t find_next_power(size_t x) {
    if (x <= 16) return 16;
    if (x <= 32) return 32;
    if (x <= 64) return 64;
    if (x <= 128) return 128;
    if (x <= 256) return 256;
    if (x <= 512) return 512;
    if (x <= 1024) return 1024;
    
    size_t power = 1;
    while (power < x) {
        power *= 2;
    }
    return power;
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) return NULL;

    // Binary 케이스 최적화: 작은 크기는 2의 제곱수로 정렬
    if (size <= CHUNKSIZE) {
        size = find_next_power(size);
    }

    // 기존 정렬 로직
    asize = (size <= DSIZE) ? 2 * DSIZE : DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = get_adaptive_chunksize(asize);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    
    place(bp, asize);
    return bp;
}


static void *find_fit(size_t asize){
    int list_num = select_list(asize);
    char *bp;
    
    // 작은 블록은 First-fit (속도 우선)
    if (asize <= 128) {
        for (int i = list_num; i < 12; i++){
            bp = seg_free_lists[i];
            while (bp != NULL){
                if (asize <= GET_SIZE(HDRP(bp))) {
                    return bp;
                }
                bp = GET_SUCC(bp);
            }
        }
        return NULL;
    }
    
    // 큰 블록은 제한된 Best-fit
    char *best_bp = NULL;
    size_t best_size = SIZE_MAX;
    int search_limit = 10;
    
    for (int i = list_num; i < 12; i++){
        bp = seg_free_lists[i];
        int count = 0;
        while (bp != NULL && count < search_limit){
            size_t block_size = GET_SIZE(HDRP(bp));
            if (asize <= block_size && block_size < best_size) {
                best_bp = bp;
                best_size = block_size;
                if (block_size == asize) return best_bp;
            }
            bp = GET_SUCC(bp);
            count++;
        }
        if (best_bp) break;
    }
    return best_bp;
}



static void place(void *bp, size_t asize) {
    size_t total = GET_SIZE(HDRP(bp));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t remainder = total - asize;

    remove_from_free_list(bp);
    
    if (remainder < 2 * DSIZE) {
        // 분할하지 않음
        PUT(HDRP(bp), PACK(total, 1, prev_alloc));
        update_next_prev_alloc(bp, 1);
    } else if (asize >= 96) {
        // 큰 블록: 뒤쪽에 할당하지 말고 앞쪽에 할당 (단순화)
        PUT(HDRP(bp), PACK(asize, 1, prev_alloc));
        
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0, 1));
        PUT(FTRP(next_bp), PACK(remainder, 0, 1));
        
        add_free_list(next_bp, remainder);
        update_next_prev_alloc(next_bp, 0);
    } else {
        // 작은 블록: 앞쪽에 할당
        PUT(HDRP(bp), PACK(asize, 1, prev_alloc));
        
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0, 1));
        PUT(FTRP(next_bp), PACK(remainder, 0, 1));
        
        add_free_list(next_bp, remainder);
        update_next_prev_alloc(next_bp, 0);
    }
}




/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

    // reallocation tag 제거
    PUT(HDRP(ptr), PACK(size, 0, prev_alloc));
    PUT(FTRP(ptr), PACK(size, 0, prev_alloc));
    
    // 다음 블록의 prev_alloc 업데이트
    void *next_bp = NEXT_BLKP(ptr);
    if (GET_SIZE(HDRP(next_bp)) != 0) {
        size_t next_size = GET_SIZE(HDRP(next_bp));
        size_t next_alloc = GET_ALLOC(HDRP(next_bp));
        PUT(HDRP(next_bp), PACK(next_size, next_alloc, 0));
    }
    
    coalesce(ptr);
}



void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t original_size = GET_SIZE(HDRP(ptr));
    size_t aligned_size;
    
    // Binary 케이스 고려한 크기 계산
    if (size <= CHUNKSIZE) {
        size = find_next_power(size);
    }
    aligned_size = (size <= DSIZE) ? 2 * DSIZE : 
                   DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
    
    // 현재 블록이 충분한 경우
    if (aligned_size <= original_size) {
        return ptr;
    }
    
    // 다음 블록과 병합 시도 (realloc-bal 최적화)
    void *next_bp = NEXT_BLKP(ptr);
    if (GET_SIZE(HDRP(next_bp)) != 0 && !GET_ALLOC(HDRP(next_bp))) {
        size_t combined_size = original_size + GET_SIZE(HDRP(next_bp));
        if (combined_size >= aligned_size) {
            remove_from_free_list(next_bp);
            
            // 정확한 크기만 사용하고 나머지는 분할
            if (combined_size - aligned_size >= MIN_BLK_SIZE) {
                PUT(HDRP(ptr), PACK(aligned_size, 1, prev_alloc));
                
                void *split_bp = (char *)ptr + aligned_size;
                size_t remaining = combined_size - aligned_size;
                PUT(HDRP(split_bp), PACK(remaining, 0, 1));
                PUT(FTRP(split_bp), PACK(remaining, 0, 1));
                add_free_list(split_bp, remaining);
                update_next_prev_alloc(split_bp, 0);
            } else {
                PUT(HDRP(ptr), PACK(combined_size, 1, prev_alloc));
                update_next_prev_alloc(ptr, 1);
            }
            return ptr;
        }
    }
    
    // 이전 블록과 병합 시도
    if (!prev_alloc) {
        void *prev_bp = PREV_BLKP(ptr);
        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        if (original_size + prev_size >= aligned_size) {
            remove_from_free_list(prev_bp);
            
            // 데이터를 앞으로 이동
            memmove(prev_bp, ptr, original_size - WSIZE);
            
            size_t total_size = original_size + prev_size;
            size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev_bp));
            
            if (total_size - aligned_size >= MIN_BLK_SIZE) {
                PUT(HDRP(prev_bp), PACK(aligned_size, 1, prev_prev_alloc));
                
                void *split_bp = (char *)prev_bp + aligned_size;
                size_t remaining = total_size - aligned_size;
                PUT(HDRP(split_bp), PACK(remaining, 0, 1));
                PUT(FTRP(split_bp), PACK(remaining, 0, 1));
                add_free_list(split_bp, remaining);
                update_next_prev_alloc(split_bp, 0);
            } else {
                PUT(HDRP(prev_bp), PACK(total_size, 1, prev_prev_alloc));
                update_next_prev_alloc(prev_bp, 1);
            }
            return prev_bp;
        }
    }
    
    // 새로 할당
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    
    size_t copySize = MIN(size, original_size - WSIZE);
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}




static void * extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

    // 이전 epilogue의 할당 상태 확인
    size_t prev_alloc = GET_ALLOC(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0, prev_alloc));
    PUT(FTRP(bp), PACK(size, 0, prev_alloc));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1, 0));

    return coalesce(bp);
}



static void *coalesce(void *bp){
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        add_free_list(bp, size);
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        void *next_bp = NEXT_BLKP(bp);
        remove_from_free_list(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0, prev_alloc));
        PUT(FTRP(bp), PACK(size, 0, prev_alloc));
        
        update_next_prev_alloc(bp, 0);
        add_free_list(bp, size);
    }
    else if (!prev_alloc && next_alloc){
        void *prev_bp = PREV_BLKP(bp);
        remove_from_free_list(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev_bp));
        
        PUT(HDRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        PUT(FTRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        bp = prev_bp;
        add_free_list(bp, size);
    }
    else{
        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);
        remove_from_free_list(prev_bp);
        remove_from_free_list(next_bp);
        
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        size_t prev_prev_alloc = GET_PREV_ALLOC(HDRP(prev_bp));
        
        PUT(HDRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        PUT(FTRP(prev_bp), PACK(size, 0, prev_prev_alloc));
        update_next_prev_alloc(prev_bp, 0);
        
        bp = prev_bp;
        add_free_list(bp, size);
    }
    return bp;
}

static void update_next_prev_alloc(void *bp, int alloc){
    void *next_bp = NEXT_BLKP(bp);
    if (GET_SIZE(HDRP(next_bp)) != 0){
        PUT(HDRP(next_bp), PACK(GET_SIZE(HDRP(next_bp)),
                                GET_ALLOC(HDRP(next_bp)), alloc));
    }
}




static void add_free_list(void *bp, size_t asize){
    int list_num = select_list(asize);
    void *first_blkp = seg_free_lists[list_num];

    SET_PRED(bp, NULL);
    SET_SUCC(bp, first_blkp);

    if (first_blkp != NULL) {
        SET_PRED(first_blkp, bp);
    }
    seg_free_lists[list_num] = bp;

}

static void remove_from_free_list(void *bp){
    if (bp == NULL) return;  // NULL 체크 추가

    void *prev_blkp = GET_PRED(bp);
    void *next_blkp = GET_SUCC(bp);

    if (prev_blkp == NULL){
        int list_num = select_list(GET_SIZE(HDRP(bp)));
        seg_free_lists[list_num] = next_blkp;
    }
    else{
        SET_SUCC(prev_blkp, next_blkp);
    }

    if (next_blkp != NULL){
        SET_PRED(next_blkp, prev_blkp);
    }
}