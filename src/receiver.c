///////////////////////////////////////
/// Hunter Adams (vha3@cornell.edu)
/// test VGA with hardware video input copy to VGA
// compile with
// gcc demodulate_fpga.c -o demod -lm -lpthread
//////////////////////////////////////
#define _GNU_SOURCE 

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/ipc.h> 
#include <sys/shm.h> 
#include <sys/mman.h>
#include <sys/time.h> 
#include <math.h> 
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h> 
#include <sched.h>
#include <time.h>

#include <errno.h>
#include <arpa/inet.h>
#include <sys/wait.h>
#include <signal.h>
#include <assert.h>

#include "receiver.h"

// threads
#include "circlebuffer.h"
#include <pthread.h>

////////////// PRN Setup ///////////////////

// The number of bits in the pseudo random number representing a 1 and 0.
#define CHIPS_PER_BIT 512

/**
 * The logical packet is the syncword + data points from a given sensor reading
 * It is subdivided into many physical packets, which are transmitted consecutively.
 */

// The number of integers in the packet to be transmitted.
#define DATA_BYTES_IN_LOGICAL_PACKET 10

// the number of bytes in our sync word
#define BYTES_IN_SYNC_WORD 4

// the number of bytes in our logical packet
#define BYTES_IN_LOGICAL_PACKET (BYTES_IN_SYNC_WORD + DATA_BYTES_IN_LOGICAL_PACKET)

// the number of chips in a logical packet. This includes garbage chips that occur
// between transmissions. Convert bytes to physical packets, and then physical packets
// to chips. A direct conversion from bytes to chips would neglect the garbage chips
#define CHIPS_PER_LOGICAL_PACKET (BYTES_IN_LOGICAL_PACKET * BITS_PER_BYTE / BITS_PER_PHYSICAL_PACKET * CHIPS_IN_PHYSICAL_PACKET)


// An estimate of the percentage of bits that will not be flipped in transmission.
#define ACCURACY_THRESHOLD 0.80

// The number of bits in a byte...
#define BITS_PER_BYTE 8

// these numbers come from our decimation/filtering approach. 
// We consume 12 samples to output a single partial chip (in a single filter),
// and it takes 3 partial chips to yeild a real one (across the 3 different filters)
#define SAMPLES_PER_CHIP (12 * 3)

// packets per buffer tells us how many packets worth of data we'll capture
// after each read_tcp call
#define PACKETS_PER_BUFFER 2

// the number of samples to collect on each read from the socket
#define SAMPLES_IN_TCP_BUFFER (SAMPLES_PER_CHIP * CHIPS_PER_LOGICAL_PACKET * PACKETS_PER_BUFFER)

// the number of chips each filter must be able to hold
#define CHIPS_IN_FILTER (CHIPS_PER_LOGICAL_PACKET * PACKETS_PER_BUFFER + 1)

// the number of data chunks in a physical packet from the transmitter
#define CHIPS_OF_DATA_IN_PHYSICAL_PACKET (BITS_PER_PHYSICAL_PACKET * CHIPS_PER_BIT)

// the sending side includes some garbage in each packet that won't transmit properly. We need to
// skip over that garbage
#define CHIPS_OF_JUNK_IN_PHYSICAL_PACKET (12 * BITS_PER_BYTE)

// the number of chunks in a physical packet
#define CHIPS_IN_PHYSICAL_PACKET (CHIPS_OF_DATA_IN_PHYSICAL_PACKET + CHIPS_OF_JUNK_IN_PHYSICAL_PACKET)

// the number of bits contained in each physical packet
#define BITS_PER_PHYSICAL_PACKET 1

int samples_in_tcp_buffer = SAMPLES_IN_TCP_BUFFER;


/**
 * Each bit is mapped to CHIPS_PER_BIT chips when being transmitted
 */


/** 16 words long, one word per line */
//defined psuedo-random number for 0.
u_char PRN0[CHIPS_PER_BIT] = {
    0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1,
    0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0,
    0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1,
    1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1,
    0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1,
    1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0,
    1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0
};

//defined psuedo-random number for 1.
u_char PRN1_CHIP_CHUNK[CHIPS_PER_BIT] = {
    1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0,
    1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1,
    1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0,
    1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0,
    0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1,
    1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0,
    0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1,
    0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1,
    1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1,
    1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1,
    1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0,
    1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1,
    1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1,
    0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1
};

/**
 * @brief A utility function for packaging bits into bytes and 
 * writing them to an output channel. The bits are buffered in 'working'
 * and when there are enough of them they get written to 'output'
 * 
 * @param bit       the bit to shift in 
 * @param output    a reference to the place we want to write complete bytes
 * @param working   a reference to an int (at least 2 bytes) for scratchwork.
 *                  should always be the same between calls. Should be initialized
 *                  to 0 or 1.
 */
void bit_funnel(int bit, char **output, int *working) {
    if (*working == 0) {
        *working = 1;
    }
    *working = *working << 1;
    if (bit) {
        *working |= 1;
    }
    if (*working & (1 << 8)) {
        **output = *working &0xff;
        (*output)++;
        *working = 0;
    }
    return;
}

/**
 * @brief A utility method for determining if two sequences of chips
 *        are close enough to be considered the same pattern. Should be a commutative
 *        operator. Uses ACCURACY_THRESHOLD to determine what constitutes a 'close enough'
 *        match.
 * 
 * @param chip_chunks_1     the first chip chunk array for comparison
 * @param chip_chunks_2     the second chip chunk array for comparison
 * @param num_chip_chunks   the number of chunks to compare across the two arrays
 * @return int              true if the sequence of chunks match, false otherwise.
 */
int chips_match(u_char *chips_1, u_char *chips_2, int num_chips) {
        int common_chips = 0; // number of chips common between sources
        for (int offset = 0; offset < num_chips; offset++) {
            common_chips += *(chips_1 + offset) == *(chips_2 + offset);
        }
        return common_chips > ACCURACY_THRESHOLD * num_chips;
}

/**
 * @brief Converts the chip chunks in 'chip_chunks' to bits via prn matching, and then
 *        aggregates those bits into bytes which get stored in 'output_bytes'
 * 
 * @param chip_chunks   the sequence of chip chunks to read from
 * @param output_bytes  the sequence of bytes to write two
 * @param num_bytes     the number of bytes of true data we want to parse out
 */
void chips_to_bytes(u_char chips[], u_char *output_bytes, int num_bytes)  {
    int working = 0;
    u_char * chip_start = chips;

    for (int bit_index = 0; bit_index < num_bytes * BITS_PER_BYTE; bit_index++) {
        // this segment leverages the fact that each physical packet carries a single bit of data
        assert(BITS_PER_PHYSICAL_PACKET == 1);
        if (chips_match(chip_start, PRN0, CHIPS_OF_DATA_IN_PHYSICAL_PACKET)) {
            bit_funnel(0, &output_bytes, &working);
        }
        else if (chips_match(chip_start, PRN1_CHIP_CHUNK, CHIPS_OF_DATA_IN_PHYSICAL_PACKET)) {
            bit_funnel(1, &output_bytes, &working);
        }
        else {
            // TODO should probably log these and eventually chuck them rather than treating as a 0
            bit_funnel(0, &output_bytes, &working);
        }
        // consume data + junk chips
        chip_start += CHIPS_OF_DATA_IN_PHYSICAL_PACKET + CHIPS_OF_JUNK_IN_PHYSICAL_PACKET;
    }
} 

////////////// END PRN SETUP /////////////////

// TCPIP buffer from RTL-SDR

char address[BYTES_IN_SYNC_WORD] = {0x07,0x07, 0x07, 0x07};

// Count received packets
int counter = 0;


circular_buffer tcpip_buffer;

/**
 * Three 'filtered arrays' to represent three potential clock synchronizations
 * The hope is that one of them will be close to synchronization, and will
 * give us good info. This pattern will be repeated for received data as well.
 */

// raw chip guesses from the 0 clock-synced buffer data
circular_buffer filtered_mod_0; 

// raw chip guesses from the 1 clock-synced buffer data
circular_buffer filtered_mod_1;

// raw chip guesses from the 2 clock-synced buffer data
circular_buffer filtered_mod_2;

// utility packaging of filtered arrays for iterating through later
circular_buffer* filtered_arrs[3] = {&filtered_mod_0, &filtered_mod_1, &filtered_mod_2};

circular_buffer packets;

#define PORT "3490"  // the port users will be connecting to
#define BACKLOG 10   // how many pending connections queue will hold

/**
 * @brief Opens up a 
 * 
 * @return void* 
 */
void * read_tcpip() {

    // =======================================================================
    // ========== Opens TCP/IP socket to RTL-SDR for I/Q sampling ============
    // =======================================================================
    int sockfd, portno, n;
    struct sockaddr_in serv_addr;
    struct hostent *server;
    unsigned int length;
    portno = atoi("1234");
    sockfd = socket(AF_INET, SOCK_STREAM, 0);
    if (sockfd < 0) 
        fprintf(stderr,"ERROR opening socket\n");
    // server = gethostbyname("192.168.1.145");
    server = gethostbyname("127.0.0.1");
    if (server == NULL) {
        fprintf(stderr,"ERROR, no such host\n");
        exit(0);
    }
    bzero((char *) &serv_addr, sizeof(serv_addr));
    serv_addr.sin_family = AF_INET;
    bcopy((char *)server->h_addr, 
         (char *)&serv_addr.sin_addr.s_addr,
         server->h_length);
    serv_addr.sin_port = htons(portno);
    if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0) 
        fprintf(stderr,"ERROR connecting\n");
    //printf("Please enter the message: ");
    length=sizeof(struct sockaddr_in);
    // =======================================================================
    // =======================================================================
    // =======================================================================
    while(1) 
    {
        u_char chunks[SAMPLES_IN_TCP_BUFFER/10];
        n = recvfrom(sockfd, chunks,
            SAMPLES_IN_TCP_BUFFER/10, MSG_WAITALL,(struct sockaddr *)&serv_addr, &length);
        cb_push_back(&tcpip_buffer, chunks, SAMPLES_IN_TCP_BUFFER/10);
    }
}

void * demodulate() {
    // variables to hold raw I/Q samples
    double first_i, first_q, second_i, second_q;
    // variables for re/im part of complex conjugate
    double real, imag;
    // array of last three arguments (θ) of complex number
    // represents phase difference between consecutive samples for the last three pairs
    double output[3];
    // finite impulse response filter taps
    double tap[3] = {0.0584283, 0.88314341, 0.0584283};
    while(1) {

        char chip_samples[SAMPLES_PER_CHIP];
        cb_pop_front(&tcpip_buffer, chip_samples, SAMPLES_PER_CHIP);

        // process the samples for a single chip
        for (int mod=0; mod < 3; mod++) {

            int filter_offset = mod * 12;
            // Decimate
            first_q =    chip_samples[filter_offset] - 128; // make samples 0-mean
            first_i =    chip_samples[filter_offset+1] - 128;
            second_q = -(chip_samples[filter_offset+6] - 128);
            second_i =   chip_samples[filter_offset+6+1] - 128;

            // Demodulate
            real = first_i*second_i - first_q*second_q; // real(z_1 * conj(z_2))
            imag = first_i*second_q + first_q*second_i; // imag(z_1 * conj(z_2))

            // update delay line
            output[0] = output[1];
            output[1] = output[2];
            output[2] = atan2(imag, real);

            // compute Finite Impulse Response
            u_char response = tap[0] * output[0] + tap[1] * output[1] + tap[2] * output[2];

            cb_push_back(filtered_arrs[mod], &response, 1);
        } // end for
    } // end while(1)
} // end task

void * search() {

    while(1) {
        int chips_in_sync_word = CHIPS_IN_PHYSICAL_PACKET / BITS_PER_PHYSICAL_PACKET * BITS_PER_BYTE * BYTES_IN_SYNC_WORD;

        // each clock tick consumes a chip. When we've consumed as many chips as the filter holds
        // we should load from the filter again.
        u_char preamble_in_chips[chips_in_sync_word];
        u_char preamble_in_bytes[BYTES_IN_SYNC_WORD];
        for (int mod_x = 0; mod_x < 3; mod_x++) {
            circular_buffer *filtered = filtered_arrs[mod_x];
            cb_peek_front(filtered, preamble_in_chips, chips_in_sync_word);
            chips_to_bytes(preamble_in_chips, preamble_in_bytes, BYTES_IN_SYNC_WORD);
            if (strcmp(preamble_in_bytes, address) == 0) {
                // fast forward the others
                cb_pop_front(filtered_arrs[(mod_x + 1) % 3], NULL, CHIPS_PER_LOGICAL_PACKET);
                cb_pop_front(filtered_arrs[(mod_x + 2) % 3], NULL, CHIPS_PER_LOGICAL_PACKET);
                // read off
                u_char packet_in_chips[CHIPS_PER_LOGICAL_PACKET];
                u_char packet[BYTES_IN_LOGICAL_PACKET];

                cb_pop_front(filtered, packet_in_chips, CHIPS_PER_LOGICAL_PACKET);
                chips_to_bytes(packet_in_chips, packet, BYTES_IN_LOGICAL_PACKET);

                // push completed packet to packets list
                cb_push_back(&packets, packet, BYTES_IN_LOGICAL_PACKET);
                break;
            }
        }
        // shift out a chip and correlate again
        for (int mod_x = 0; mod_x < 3; mod_x++) {
            cb_pop_front(filtered_arrs[mod_x], NULL, 1);
        }
    }
}

int connection = -1;

void * exfiltrate() {
    FILE *fp;
    time_t now;

    int i;
    while(1) {
        u_char packet[BYTES_IN_LOGICAL_PACKET];
        cb_pop_front(&packets, packet, BYTES_IN_LOGICAL_PACKET);

        counter += 1;
        printf("%d: ", counter);
        fp = fopen("stored_data.txt", "a+");
        time(&now);
        for (i=0; i<BYTES_IN_LOGICAL_PACKET; i++) {
            printf("%02x ", packet[i]);
            fprintf(fp, "%02x ", packet[i]);
        }
        fprintf(fp, "%s", ctime(&now));
        fclose(fp);
        printf("\n");
    }
}


// int main(void)
// {

//     circular_buffer tcpip_buffer;
//     cb_init(&tcpip_buffer, SAMPLES_IN_TCP_BUFFER, sizeof(u_char));
//     cb_init(&filtered_mod_0, CHIPS_IN_FILTER, sizeof(u_char));
//     cb_init(&filtered_mod_1, CHIPS_IN_FILTER, sizeof(u_char));
//     cb_init(&filtered_mod_2, CHIPS_IN_FILTER, sizeof(u_char));
//     cb_init(&packets, 10, sizeof(u_char));

//     //For portability, explicitly create threads in a joinable state 
//     // thread attribute used here to allow JOIN
//     pthread_attr_t attr;
//     pthread_attr_init(&attr);
//     pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

//     // now the threads
//     // the thread identifiers
//     pthread_t thread_read, thread_demodulate, thread_search, thread_exfiltrate ;
//     pthread_create(&thread_read,NULL,read_tcpip, NULL);
//     pthread_create(&thread_demodulate, NULL, demodulate, NULL);
//     pthread_create(&thread_search,NULL,search,NULL);
//     pthread_create(&thread_exfiltrate,NULL, exfiltrate,NULL);

//     // In this case the thread never exit
//     pthread_join(thread_read,NULL);
//     pthread_join(thread_demodulate,NULL);
//     pthread_join(thread_search,NULL);
//     pthread_join(thread_exfiltrate,NULL);
//     return 0;
// } // end main