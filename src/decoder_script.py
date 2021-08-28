
import timeit
gold1_st = "11111101001111100111011111010101001001011110111100101100011010" \
    "010010101011101001001111001100010000000111100100111100010100000" \
    "1110011011100011111011110111101000110111010000001111001000000110" \
    "1111101111101011010111011011100100010001100011010011001011100101" \
    "0011010110011011001110101100001101011010110101010000000010111010" \
    "01101101010110010111101011001010010001111111110011110000010100001" \
    "10011011101001101001100101101001100010111001010100111101000111101" \
    "01100101100101110011000111011111101010100110001001101010001010100"


gold0_st = "00000001010111101101010001100001000010111111001100110001010111000110011" \
    "01001001001011011001010101110000010100011000000001110000110111011100111" \
    "11001100011100111111110111110000001011001001110101101010101010011110100" \
    "10100010010000011110101101100000010001111010100111001100000100011100001" \
    "011100110100100001010110000101000101000001101010001000110110001011111010" \
    "100100011111110101111111110110011101010010000001100100011000101011110011" \
    "011010010011000000000001000010000101001010000001110101011100101011110110" \
    "010011011010"


gold0_st = "0" * 512

gold1_st = "1" * 512
accuracy_threshold = 98
start_time = 0


def extract_data(file_path):
    with open(file_path) as f:
        lines = f.readlines()
    all_data = []
    for line in lines:
        line_data = line.split()
        all_data.append(line_data)

    # print(all_data)
    sequence = ""
    for data in all_data:
        for num in data:
            # print(data)
            if num == "00":
                sequence += "0"
            elif num == "01":
                sequence += "1"

    return sequence


def get_match(window):
    match_0 = 0
    match_1 = 0
    for i in range(len(window)):
        if window[i] == gold0_st[i]:
            match_0 += 1
        if window[i] == gold1_st[i]:
            match_1 += 1

    if (match_0/len(window)) * 100 > accuracy_threshold:
        return 0
    elif (match_1/len(window)) * 100 > accuracy_threshold:
        return 1
    return -1


def get_starts(st):
    count = 0
    final_mapped = []
    start_indices = []
    while(count < len(st) - 512):
        window = st[count:count + 512]
        result = get_match(window)
        if result == 0 or result == 1:
            final_mapped.append(result)
            start_indices.append(count)
            count += 512
        else:
            count += 1
    # print(start_indices)
    return final_mapped


def find_start(mapped_bits):
    """
    Looking for sync word to see how to pair bits 
    """
    for i in range(len(mapped_bits)-8):
        str1 = ""
        for num in mapped_bits[i:i+8]:
            str1 += str(num)
        # checking for 197
        if str1 == "11000101":
            print("Start", i)
            return i
    print("Not found")
    return 0


def decrypt_revised(file_path):
    st = extract_data(file_path)
    start_time = timeit.default_timer()
    decrypted_data = []
    mapped = get_starts(st)
    count = 0
    byte_data = ""
    start = find_start(mapped)
    for i in range(start, len(mapped)):
        byte_data += str(mapped[i])
        count += 1
        if (count % 8 == 0):
            try:
                decrypted_data.append(int(byte_data, 2))
            except:
                decrypted_data.append(23)
            byte_data = ""

    return decrypted_data


print(decrypt_revised('data_filepath'))
stop_time = timeit.default_timer()
print((stop_time - start_time))
