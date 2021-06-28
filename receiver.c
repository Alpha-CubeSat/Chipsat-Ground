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

// threads
#include <pthread.h>
#include <semaphore.h>  

////////////// PRN Setup ///////////////////

// The number of bits in the pseudo random number representing a 1 and 0.
#define CHIPS_PER_BIT 512

// The number of integers in the packet to be transmitted.
#define BYTES_PER_PACKET 10

// An estimate of the percentage of bits that will not be flipped in transmission.
#define ACCURACY_THRESHOLD 0.80

// The number of bits in a byte...
#define BITS_PER_BYTE 8

// the number of chips in a chip-chunk. Currently 8 for char chunks, but could be
// 16, 32 etc if we want to move to larger chunk containers.
#define CHIPS_PER_CHIP_CHUNK 8

// the number of bytes in our sync word (not really a word anymore)
#define BYTES_IN_SYNC_WORD 3

// the number of chips in the packet
#define CHIPS_PER_PACKET (CHIPS_PER_BIT * BITS_PER_BYTE * BYTES_PER_PACKET)

// these numbers come from our decimation/filtering approach. 
// We consume 12 samples to output a single partial chip (in a single filter),
// and it takes 3 partial chips to yeild a real one (across the 3 different filters)
#define SAMPLES_PER_CHIP (12 * 3)

// packets per buffer tells us how many packets worth of data we'll capture
// after each read_tcp call
#define PACKETS_PER_BUFFER 2

// the number of samples to collect on each read from the socket
#define SAMPLES_IN_TCP_BUFFER (SAMPLES_PER_CHIP * CHIPS_PER_PACKET * PACKETS_PER_BUFFER)

// the number of chips each filter must be able to hold
#define CHIPS_IN_FILTER (CHIPS_PER_PACKET * PACKETS_PER_BUFFER + 1)

// the number of chunks in our received_arr.
// note that whatever size we choose, it will be depleted by CHIPS_IN_FILTER
// chips before the next refill.
#define CHUNKS_IN_RECEIVED (CHIPS_IN_FILTER * 2 / CHIPS_PER_CHIP_CHUNK)

/**
Each bit is mapped to CHIPS_PER_BIT chips when being transmitted
Each packet contains [BYTES_PER_PACKET] integers of 8 bits.
Total size = 8 * BYTES_PER_PACKET * CHIPS_PER_BIT
*/


//defined psuedo-random number for 0.
char PRN0_STRING[CHIPS_PER_BIT] = "11111101001111100111011111010101001001011110111100101100011010"
                      "010010101011101001001111001100010000000111100100111100010100000"
                      "1110011011100011111011110111101000110111010000001111001000000110"
                      "1111101111101011010111011011100100010001100011010011001011100101"
                      "0011010110011011001110101100001101011010110101010000000010111010"
                      "01101101010110010111101011001010010001111111110011110000010100001"
                      "10011011101001101001100101101001100010111001010100111101000111101"
                      "01100101100101110011000111011111101010100110001001101010001010100";

//defined psuedo-random number for 1.
char PRN1_STRING[CHIPS_PER_BIT] = "00000001010111101101010001100001000010111111001100110001010111000110011"
                      "01001001001011011001010101110000010100011000000001110000110111011100111"
                      "11001100011100111111110111110000001011001001110101101010101010011110100"
                      "10100010010000011110101101100000010001111010100111001100000100011100001"
                      "011100110100100001010110000101000101000001101010001000110110001011111010"
                      "100100011111110101111111110110011101010010000001100100011000101011110011"
                      "011010010011000000000001000010000101001010000001110101011100101011110110"
                      "010011011010";

// prn0 chip sequences packaged into chip-chunks (chars of 8 chips)
char PRN0_CHIP_CHUNK[CHIPS_PER_BIT / 8];

// prn1 chip sequences packaged into chip-chunks (chars of 8 chips)
char PRN1_CHIP_CHUNK[CHIPS_PER_BIT / 8];

/**
 * @brief takes in a prn-string and converts it into a chunk array
 * 
 * @param prn               input prn string of 0s and 1s
 * @param prn_chip_chunks   output 
 */
void generate_chip_chunks(char prn[], char prn_chip_chunks[]) {
    int working = 0;
    for (int chip_index = 0; chip_index < CHIPS_PER_BIT; chip_index++) {

        switch(prn[chip_index]) {
            case '0':
                bit_funnel(0, &prn_chip_chunks, &working);
                break;
            case '1':
                bit_funnel(1, &prn_chip_chunks, &working);
                break;
            default:
                throw("poorly formatted prn");
        }
    }
}

/**
 * @brief A utility array that is used for quickly determining 
 * the number of set bits in a chunk. For example:
 * 5 = 0b101 goes to 2.
 */
int INTERFERENCE_LOOKUP[1 << CHIPS_PER_CHIP_CHUNK];

/**
 * @brief Populates the INTERFERENCE_LOOKUP array above.
 */
void generate_interference_lookup() {
    int interference_lookup_length = 1 << CHIPS_PER_CHIP_CHUNK;
    for (int index = 0; index < interference_lookup_length; index++) {
        int num_copy = index; // copy so that we don't mutate the thing over which we iterate 
        int set_bits_in_num = 0; // count of bits set in the 
        while (num_copy) {
            num_copy &= (num_copy - 1);
            set_bits_in_num += 1;
        }
        INTERFERENCE_LOOKUP[index] = set_bits_in_num;
    }
}

/**
 * @brief TODO test this!! I tried, but it wasn't working, which isn't
 * a good sign... A utility function for packaging bits into bytes and 
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
 * @brief A utility method for determining if two sequences of chip chunks represent
 *        are close enough to be considered the same pattern. Should be a commutative
 *        operator. Uses ACCURACY_THRESHOLD to determine what constitutes a 'close enough'
 *        match.
 * 
 * @param chip_chunks_1     the first chip chunk array for comparison
 * @param chip_chunks_2     the second chip chunk array for comparison
 * @param num_chip_chunks   the number of chunks to compare across the two arrays
 * @return int              true if the sequence of chunks match, false otherwise.
 */
int chip_chunks_match(char *chip_chunks_1, char *chip_chunks_2, int num_chip_chunks) {
        int common_chips = 0; // number of chips common between sources
        for (int offset = 0; offset < num_chip_chunks; offset++) {
            // the ith index of ~(x^y) is true iff x[i] == y[i]
            char interference_pattern = ~ (chip_chunks_1[offset] ^ chip_chunks_2[offset]);
            common_chips += INTERFERENCE_LOOKUP[interference_pattern];
        }
        int max_common = num_chip_chunks * CHIPS_PER_CHIP_CHUNK;
        return ((float) common_chips / max_common) > ACCURACY_THRESHOLD;
}

/**
 * @brief Converts the chip chunks in 'chip_chunks' to bits via prn matching, and then
 *        aggregates those bits into bytes which get stored in 'output_bytes'
 * 
 * @param chip_chunks   the sequence of chip chunks to read from
 * @param output_bytes  the sequence of bytes to write two
 * @param num_bytes     the number of bytes we want to parse out
 */
void chip_chunks_to_bytes(char chip_chunks[], char output_bytes[], char num_bytes) {
    // this division is a little scary, not sure what happens if there's a remainder
    int num_chip_chunks = num_bytes * BITS_PER_BYTE * CHIPS_PER_BIT / CHIPS_PER_CHIP_CHUNK;
    int chip_chunk_index = 0;
    int chip_chunks_per_bit = CHIPS_PER_BIT / CHIPS_PER_CHIP_CHUNK;

    int working = 0;
    while (chip_chunk_index < num_chip_chunks) {
        if (chip_chunks_match(chip_chunks[chip_chunk_index], PRN0_CHIP_CHUNK, chip_chunks_per_bit)) {
            bit_funnel(0, &output_bytes, &working);
        }
        else if (chip_chunks_match(chip_chunks[chip_chunk_index], PRN1_CHIP_CHUNK, chip_chunks_per_bit)) {
            bit_funnel(1, &output_bytes, &working);
        }
        else {
            // TODO should probably log these and eventually chuck them rather than treating as a 0
            bit_funnel(0, &output_bytes, &working);
        }
        chip_chunk_index += chip_chunks_per_bit;
    }
} 


////////////// END PRN SETUP /////////////////



// Semaphores for flow control
sem_t tcpip_semaphore;
sem_t slice_semaphore;
sem_t search_semaphore;
sem_t check_semaphore;
sem_t start_semaphore;
sem_t exfiltrate_semaphore;

// TCPIP buffer from RTL-SDR
unsigned char tcpip_buffer[SAMPLES_IN_TCP_BUFFER];

/**
 * Three 'filtered arrays' to represent three potential clock synchronizations
 * The hope is that one of them will be close to synchronization, and will
 * give us good info. This pattern will be repeated for received data as well.
 */

// raw chip guesses from the 0 clock-synced buffer data
int filtered_mod_0[CHIPS_IN_FILTER]; 
// raw chip guesses from the 1 clock-synced buffer data
int filtered_mod_1[CHIPS_IN_FILTER];
// raw chip guesses from the 2 clock-synced buffer data
int filtered_mod_2[CHIPS_IN_FILTER];

// utility packaging of filtered arrays for iterating through later
int **filtered_arrs = {filtered_mod_0, filtered_mod_1, filtered_mod_2};

// processed chunk array from the 0 clock-synced buffer data
char received_test_0[CHUNKS_IN_RECEIVED];
// processed chunk array from the 1 clock-synced buffer data
char received_test_1[CHUNKS_IN_RECEIVED];
// processed chunk array from the 2 clock-synced buffer data
char received_test_2[CHUNKS_IN_RECEIVED];

// utility packaging of chunk-arrays for iterating through later
char **received_test_arrs = {received_test_0, received_test_1, received_test_2};

// Sync word (actually not a word anymore...) TODO replace with real sync word
char address[BYTES_IN_SYNC_WORD] = {0xff,0x00, 0xff};

// Count received packets
int counter = 0;

// location for keeping received packets
char packet[BYTES_PER_PACKET];

// tracks how many times we've shifted the received_test_x arrays. Each shift
// removes a chip. When we've removed enough chips, read more data from the socket
// and pass them through. 
int numclocks;

#define PORT "3490"  // the port users will be connecting to
#define BACKLOG 10   // how many pending connections queue will hold

/**
 * @brief Used to shift the entire chip_chunk array left a single chip so 
 * that the most significant chips is shifted out and a 0 is shifted in. 
 * This requires shifting across chunk boundaries.
 * 
 * @param array 
 */
void clock_array(char array[CHUNKS_IN_RECEIVED]) {
    for(int i=0; i<CHUNKS_IN_RECEIVED; i++) {
        array[i] = ((array[i] << 1) & 0xff) | ((array[i+1] & 0x80) >> 7);
    }
    array[CHUNKS_IN_RECEIVED] = ((array[CHUNKS_IN_RECEIVED] << 1) & 0xff); // shift in a 0--doesn't actually matter
}

/**
 * @brief Opens up a 
 * 
 * @return void* 
 */
void * read_tcpip() {

    sem_wait(&start_semaphore);

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
    bzero(tcpip_buffer, SAMPLES_IN_TCP_BUFFER);
    length=sizeof(struct sockaddr_in);
    // =======================================================================
    // =======================================================================
    // =======================================================================


    // variables to hold raw I/Q samples
    double first_i, first_q, second_i, second_q;
    // variables for re/im part of complex conjugate
    double real, imag;
    // array of last three arguments (θ) of complex number
    // represents phase difference between consecutive samples for the last three pairs
    double output[3];
    // finite impulse response filter taps
    double tap[3] = {0.0584283, 0.88314341, 0.0584283};


    while(1) 
    {

        sem_wait(&tcpip_semaphore);
        bzero(tcpip_buffer,SAMPLES_IN_TCP_BUFFER);

        n = recvfrom(sockfd, tcpip_buffer,
            SAMPLES_IN_TCP_BUFFER, MSG_WAITALL,(struct sockaddr *)&serv_addr, &length);

        if (n > 0) {
            // variables for sample rates in TCPIP buffer
            for (int buffer_index=0, response_index = 0; buffer_index<n; buffer_index+=12, response_index++) {

                // Decimate
                first_q =    tcpip_buffer[buffer_index] - 128; // make samples 0-mean
                first_i =    tcpip_buffer[buffer_index+1] - 128;
                second_q = -(tcpip_buffer[buffer_index+6] - 128);
                second_i =   tcpip_buffer[buffer_index+6+1] - 128;

                // Demodulate
                real = first_i*second_i - first_q*second_q; // real(z_1 * conj(z_2))
                imag = first_i*second_q + first_q*second_i; // imag(z_1 * conj(z_2))

                // update delay line
                output[0] = output[1];
                output[1] = output[2];
                output[2] = atan2(imag, real);

                // compute Finite Impulse Response
                int response = tap[0] * output[0] + tap[1] * output[1] + tap[2] * output[2];
                
                // Sift response into appropriate clock-synced array
                filtered_arrs[response_index % 3][response_index / 3] = response;
            }
            sem_post(&slice_semaphore);
            n = 0;
        } // end if
    } // end while(1)
} // end task


void * slice() {

    while(1) {

        sem_wait(&slice_semaphore);

        // we're appending new data to the END of the buffered chip-chunks
        int chunk_offset = CHUNKS_IN_RECEIVED - CHIPS_IN_FILTER / CHIPS_PER_CHIP_CHUNK;

        int working = 0; 
        for (int filter_num = 0; filter_num < 3; filter_num++) {
            int *filter = filtered_arrs[filter_num];
            char *received_test = received_test_arrs[filter_num] + chunk_offset;

            for (int index = 0; index<CHIPS_IN_FILTER; index++){
                bit_funnel(filter[index] > 0, &received_test, &working);
            }
        }

        // you'll pop bitstrings over to FPGA here
        numclocks = 0;
        sem_post(&search_semaphore);
    }
}

void * search() {

    while(1) {

        sem_wait(&search_semaphore);

        // TODO redesign this so we don't need to shift every single byte of the array. A more
        // performant implementation would be to shift the location at which we index into the
        // array. The words 'ring buffer' come to mind, but not sure that's right

        // each clock tick consumes a chip. When we've consumed as many chips as the filter holds
        // we should load from the filter again.
        while (numclocks < CHIPS_IN_FILTER) {
            char preamble[BYTES_IN_SYNC_WORD];
            for (int mod_x = 0; mod_x < 3; mod_x++) {
                char *received_test = received_test_arrs[mod_x];
                chip_chunks_to_bytes(received_test, preamble, BYTES_IN_SYNC_WORD);
                if (strcmp(preamble, address) == 0) {
                    chip_chunks_to_bytes(received_test + BYTES_IN_SYNC_WORD, packet, BYTES_PER_PACKET);
                    sem_post(&exfiltrate_semaphore);
                    sem_wait(&search_semaphore);
                }
                clock_array(received_test);
            }
            // bzero(packet, 78); not sure why we needed this...
            numclocks += 1;
        }
        sem_post(&tcpip_semaphore);
    }
}

int connection = -1;
void * exfiltrate() {
    FILE *fp;
    time_t now;

    int i;

    sem_post(&start_semaphore);

    while(1) {

        sem_wait(&exfiltrate_semaphore);

        counter += 1;
        printf("%d: ", counter);
        fp = fopen("stored_data.txt", "a+");
        time(&now);
        for (i=0; i<=BYTES_PER_PACKET; i++) {
            printf("%02x ", packet[i]);
            fprintf(fp, "%02x ", packet[i]);
        }
        fprintf(fp, "%s", ctime(&now));
        fclose(fp);
        printf("\n");

        // fast forward clocks to consume chips included in packet
        for (i=0; i<(BYTES_PER_PACKET*BITS_PER_BYTE); i++) {
            clock_array(received_test_0);
            clock_array(received_test_1);
            clock_array(received_test_2);
        }
        numclocks += BYTES_PER_PACKET*BITS_PER_BYTE;

        sem_post(&search_semaphore);
    }
}


int main(void)
{

    // since we're going to be refilling the received_arr from the filterarrs, we need
    // to be sure that even when we're most depleted, we have enough valid chips left to
    // do good processing
    assert(CHUNKS_IN_RECEIVED * CHIPS_PER_CHIP_CHUNK > CHIPS_IN_FILTER + CHIPS_PER_PACKET);
    generate_chip_chunks(PRN0_STRING ,PRN0_CHIP_CHUNK);
    generate_chip_chunks(PRN1_STRING, PRN1_CHIP_CHUNK);
    generate_interference_lookup();

    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);  
    // put two processsors into the list
    CPU_SET(0, &cpuset);
    CPU_SET(1, &cpuset);
    CPU_SET(2, &cpuset);
    CPU_SET(3, &cpuset);

    // the thread identifiers
    pthread_t thread_read, thread_demodulate, thread_filter, thread_search, thread_slice, thread_exfiltrate ;

    // the semaphore inits
    sem_init(&tcpip_semaphore, 0, 1);
    sem_init(&search_semaphore, 0, 0);
    sem_init(&slice_semaphore, 0, 0);
    sem_init(&check_semaphore, 0, 0);
    sem_init(&start_semaphore, 0, 0);
    sem_init(&exfiltrate_semaphore, 0, 0);

    //For portability, explicitly create threads in a joinable state 
    // thread attribute used here to allow JOIN
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_JOINABLE);

    // now the threads
    pthread_create(&thread_read,NULL,read_tcpip,NULL);
    pthread_create(&thread_search,NULL,search,NULL);
    pthread_create(&thread_slice,NULL,slice,NULL);
    pthread_create(&thread_exfiltrate,NULL, exfiltrate,NULL);

    // for efficiency, force  threads onto separate processors
    pthread_setaffinity_np(thread_read, sizeof(cpu_set_t), &cpuset);
    pthread_setaffinity_np(thread_search, sizeof(cpu_set_t), &cpuset);
    pthread_setaffinity_np(thread_slice, sizeof(cpu_set_t), &cpuset);
    pthread_setaffinity_np(thread_exfiltrate, sizeof(cpu_set_t), &cpuset);

    // In this case the thread never exit
    pthread_join(thread_read,NULL);
    pthread_join(thread_search,NULL);
    pthread_join(thread_slice,NULL);
    pthread_join(thread_exfiltrate,NULL);
    return 0;
} // end main