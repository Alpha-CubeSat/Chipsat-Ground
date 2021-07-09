
#include <errno.h>
#include <sys/wait.h>
#include <signal.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <semaphore.h>  
#include <unistd.h>
#include <string.h>
#include "circlebuffer.h"


// taken from https://stackoverflow.com/questions/827691/how-do-you-implement-a-circular-buffer-in-c

void cb_init(circular_buffer *cb, size_t capacity, size_t sz)
{
    cb->buffer = malloc(capacity * sz);
    if(cb->buffer == NULL) {
        printf("malloc failed");
        exit(1);
    }
    cb->buffer_end = (char *)cb->buffer + capacity * sz;
    cb->capacity = capacity;
    cb->count = 0;
    cb->sz = sz;
    cb->head = cb->buffer;
    cb->tail = cb->buffer;

    pthread_cond_init(&cb->not_empty_condition, NULL);
    pthread_cond_init(&cb->not_full_condition, NULL);
    pthread_mutex_init(&cb->lock, NULL);
}

void cb_free(circular_buffer *cb)
{
    free(cb->buffer);
    pthread_cond_destroy(&cb->not_empty_condition);
    pthread_cond_destroy(&cb->not_full_condition);
    pthread_mutex_destroy(&cb->lock);
}

void cb_push_back(circular_buffer *cb, const void *item, int length)
{
    if (length > cb->capacity) {
        printf("can't write that much to the buffer");
        fflush(stdout);
        exit(1);
    }
    // making this atomic could get us into trouble..
    pthread_mutex_lock(&cb->lock);
    while(cb->count + length > cb->capacity){
        pthread_cond_wait(&cb->not_full_condition, &cb->lock);
    }
    // we can try to get more clever about this part later
    for (int offset = 0; offset < length; offset++) {
        memcpy(cb->tail, item + offset * cb->sz, cb->sz);
        cb->tail = (char*)cb->tail + cb->sz;
        if(cb->tail == cb->buffer_end)
            cb->tail = cb->buffer;
        cb->count++;
    }

    pthread_cond_signal(&cb->not_empty_condition);
    pthread_mutex_unlock(&cb->lock);
}

void cb_peek_front(circular_buffer *cb, void *item, int length)
{
    if (length > cb->capacity) {
        printf("can't read that much from the buffer");
        exit(1);
    }
    pthread_mutex_lock(&cb->lock);
    while(cb->count < length){
        pthread_cond_wait(&cb->not_empty_condition, &cb->lock);
    }

    void * copy_from = cb->head;
    for (int offset = 0; offset < length; offset++) {
        memcpy(item + offset * cb->sz, copy_from, cb->sz);
        copy_from += cb->sz;
        if (copy_from == cb->buffer_end) {
            copy_from = cb->buffer;
        }
    }

    pthread_mutex_unlock(&cb->lock);
}

void cb_pop_front(circular_buffer *cb, void *item, int length)
{
    if (length > cb->capacity) {
        printf("can't read that much from the buffer");
        exit(1);
    }
    while(cb->count < length){
        pthread_cond_wait(&cb->not_empty_condition, &cb->lock);
    }

    for (int offset = 0; offset < length; offset++) {
        if (item != NULL) {
            memcpy(item + offset * cb->sz, cb->head, cb->sz);
        }
        cb->head = (char*)cb->head + cb->sz;
        if(cb->head == cb->buffer_end)
            cb->head = cb->buffer;
        cb->count--;
    }
    pthread_cond_signal(&cb->not_full_condition);
    pthread_mutex_unlock(&cb->lock);
}