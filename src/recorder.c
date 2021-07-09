#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <pthread.h>

#include "receiver.h"


extern circular_buffer tcpip_buffer;
extern int samples_in_tcp_buffer;

int done = 0;

void sig_handler(int signum){
    done = 1;
}

void * write_out() {
    FILE *fp;
    signal(SIGINT, sig_handler);

    fp = fopen("recorded_data.txt", "a+");
    while(!done) {
        char data[100];
        cb_pop_front(&tcpip_buffer, data, 100);
        for (int i=0; i<100; i++) {
            fprintf(fp, "%02x\n", data[i]);
        }
    }
    fclose(fp);
    exit(1);
}

int main() {
    pthread_t thread_read, thread_write_out;
    
    cb_init(&tcpip_buffer, samples_in_tcp_buffer, sizeof(char));

    pthread_create(&thread_read,NULL,read_tcpip, NULL);
    pthread_create(&thread_write_out,NULL, write_out, NULL);

    // In this case the thread never exit
    pthread_join(thread_read,NULL);
    pthread_join(thread_write_out,NULL);
    return 0;
}