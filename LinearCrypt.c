#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <stdlib.h>
#include <time.h>

#define WORD32 unsigned int
#define BYTE unsigned char

#define ROUNDS 4
#define MAX_LEN 256
#define PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT 200 
#define OUTER_SEARCH 4096
#define INNER_SEARCH 1048576

#define ROT2(x) (((x) << 2) | ((x) >> 6))

#define G0(a, b) (ROT2((BYTE)((a) + (b))))
#define G1(a, b) (ROT2((BYTE)((a) + (b) + 1)))

unsigned int LEFT0, RIGHT0, LEFT4, RIGHT4;
int count_plaintext_ciphertext_pairs = PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT;

char plain_text[PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT][18];
char cipher_text[PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT][18];
time_t start_time;
time_t end_time;
int TOTAL_KEYS_FOUND = 0;

void seperate_left_and_right_L_R(int idx)
{
    char tmp[8];
    size_t bytes = 8;
    char *hex;

    // printf("%d %s\n", idx, plain_text[idx]);
    // hex = strncpy(tmp, plain_text[idx], bytes);
    // printf("%s\n", hex);

    LEFT0 = (unsigned int)strtol(strncpy(tmp, plain_text[idx], bytes), NULL, 16);
    RIGHT0 = (unsigned int)strtol(strncpy(tmp, plain_text[idx] + 8, bytes), NULL, 16);
    LEFT4 = (unsigned int)strtol(strncpy(tmp, cipher_text[idx], bytes), NULL, 16);
    RIGHT4 = (unsigned int)strtol(strncpy(tmp, cipher_text[idx] + 8, bytes), NULL, 16);
}

void read_plaintext_ciphertext_pairs_from_file()
{

    char *file_name = "known.txt";
    FILE *file_ptr = fopen(file_name, "r");

    if (file_ptr == NULL)
    {
        perror("Failed: ");
    }

    struct stat file_stat;
    stat("known.txt", &file_stat);

    char buffer[100];
    int ctr = 1;
    int i = 0, j = 0, k = 0;
    char *temp;
    while (fgets(buffer, 100, file_ptr) != NULL)
    {
        if (ctr % 3 == 1)
        {
            strcpy(plain_text[i++], buffer + 12);
        }
        else if (ctr % 3 == 2)
        {
            strcpy(cipher_text[j++], buffer + 12);
        }
        ctr++;
    }
    fclose(file_ptr);
    // seperate_left_and_right_L_R(100);
}

static WORD32 pack32(BYTE *b)
{ /* pack 4 bytes into a 32-bit Word */
    return (WORD32)b[3] | ((WORD32)b[2] << 8) | ((WORD32)b[1] << 16) | ((WORD32)b[0] << 24);
}

static void unpack32(WORD32 a, BYTE *b)
{ /* unpack bytes from a 32-bit word */
    b[0] = (BYTE)(a >> 24);
    b[1] = (BYTE)(a >> 16);
    b[2] = (BYTE)(a >> 8);
    b[3] = (BYTE)a;
}

WORD32 f(WORD32 input)
{
    BYTE x[4], y[4];
    unpack32(input, x);
    y[1] = G1(x[1] ^ x[0], x[2] ^ x[3]);
    y[0] = G0(x[0], y[1]);
    y[2] = G0(y[1], x[2] ^ x[3]);
    y[3] = G1(y[2], x[3]);
    return pack32(y);
}

void encrypt(BYTE data[8], WORD32 key[6])
{
    WORD32 left, right, temp;

    left = pack32(&data[0]);
    right = left ^ pack32(&data[4]);

    for (int i = 0; i < ROUNDS; i++)
    {
        temp = right;
        right = left ^ f(right ^ key[i]);
        left = temp;
    }

    temp = left;
    left = right ^ key[4];
    right = temp ^ right ^ key[5];

    unpack32(left, &data[0]);
    unpack32(right, &data[4]);
}

void decrypt(BYTE data[8], WORD32 key[6])
{
    WORD32 left, right, temp;

    right = pack32(&data[0]) ^ key[4];
    left = right ^ pack32(&data[4]) ^ key[5];

    for (int i = 0; i < ROUNDS; i++)
    {
        temp = left;
        left = right ^ f(left ^ key[ROUNDS - 1 - i]);
        right = temp;
    }

    right ^= left;

    unpack32(left, &data[0]);
    unpack32(right, &data[4]);
}

/* Not the key you are looking for!!! */
WORD32 key[6] = {0x0, 0x0, 0x0, 0x0, 0x0, 0x0};

int extract_nth_bit(int num, int n)
{
    return (num >> (31 - n)) & 1;
}

int twelve_bit_key(int reduced_key_permutations)
{
    return (((reduced_key_permutations >> 6) & 0x3F) << 16) + ((reduced_key_permutations & 0x3F) << 8);
}

int permute_twenty_bits_with_k_prime(int possibile_key_match, int reduced_key_prime)
{
    int operand0 = (((possibile_key_match & 0xF) >> 2) << 6) + ((reduced_key_prime >> 16) & 0xFF);
    int operand1 = ((possibile_key_match & 0x3) << 6) + ((reduced_key_prime >> 8) & 0xFF);

    int byte0 = (possibile_key_match >> 12) & 0xFF;
    int byte3 = (possibile_key_match >> 4) & 0xFF;

    int byte1 = byte0 ^ operand0;
    int byte2 = byte3 ^ operand1;

    return (byte0 << 24) + (byte1 << 16) + (byte2 << 8) + byte3;
}

int reverse_bytes(int n)
{

    int result;
    result = ((n & 0xFF) << 24) + (((n >> 8) & 0xFF) << 16) + (((n >> 16) & 0xFF) << 8) + (((n >> 24) & 0xFF) << 0);
    return result;
}

void generate_K_4_K_5_and_matching_sets_of_keys(int possible_key_0, int possible_key_1, int possible_key_2, int possible_key_3)
{

    int round_fun_0_res = f(LEFT0 ^ RIGHT0 ^ possible_key_0);
    int round_fun_1_res = f(LEFT0 ^ round_fun_0_res ^ possible_key_1);
    int round_fun_2_res = f(LEFT0 ^ RIGHT0 ^ round_fun_1_res ^ possible_key_2);
    int round_fun_3_res = f(LEFT0 ^ round_fun_0_res ^ round_fun_2_res ^ possible_key_3);
    int ctr = 0;
    int i;

    possible_key_0 = reverse_bytes(possible_key_0);
    possible_key_1 = reverse_bytes(possible_key_1);
    possible_key_2 = reverse_bytes(possible_key_2);
    possible_key_3 = reverse_bytes(possible_key_3);
    int possible_key_4 = reverse_bytes(LEFT0 ^ RIGHT0 ^ round_fun_1_res ^ round_fun_3_res ^ LEFT4);
    int possible_key_5 = reverse_bytes(RIGHT0 ^ round_fun_1_res ^ round_fun_3_res ^ round_fun_0_res ^ round_fun_2_res ^ RIGHT4);

    unsigned int key[] = {possible_key_0, possible_key_1, possible_key_2, possible_key_3, possible_key_4, possible_key_5};

    unsigned char data[8];
    // unsigned char tmp[2];

    char tmp[3];
    size_t bytes = 2;
    char *hex;

    for (ctr = 0; ctr < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; ctr++)
    {

        for (i = 0; i < 8; i++)
        {

            strncpy(tmp, cipher_text[ctr] + i * 2, bytes);
            tmp[2] = '\0';
            data[i] = (unsigned char)((int)strtol(tmp, NULL, 16) & 255);
        }

        decrypt(data, key);

        const size_t arrlen = sizeof(data);
        const size_t hexlen = 2; // hex representation of byte with leading zero
        const size_t outstrlen = arrlen * 2;

        char *outstr = malloc(outstrlen + 1);

        // Create a string containing a hex representation of `bytearr`
        char *p = outstr;
        for (size_t i = 0; i < arrlen; i++)
        {
            p += sprintf(p, "%02x", data[i]);
        }

        if (strcmp(plain_text[ctr], outstr) == 0)
        {
            return;
        }
        free(outstr);
    }
    time(&end_time);
    if (TOTAL_KEYS_FOUND == 0)
        printf("Time taken to find first key combination((K0...K5)): %0.4f seconds\n", difftime(end_time, start_time));
    ++TOTAL_KEYS_FOUND;

    printf("K0: 0x%02x K1: 0x%02x K2: 0x%02x K3: 0x%02x K4: 0x%02x K5: 0x%02x\n", possible_key_0, possible_key_1, possible_key_2, possible_key_3, possible_key_4, possible_key_5);
}

int test_k_3_against_equation_1(int wordIndex, int key, int k0, int k1, int k2)
{
    seperate_left_and_right_L_R(wordIndex);

    // operand1 = S5,13,21(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand1 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 5) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 13) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 21);

    // operand2 = S15(LEFT0 ⊕ RIGHT0 ⊕ LEFT4)
    int operand2 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 15);

    // operand3 = S15 F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1) ⊕ K2) ⊕ K3)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int y1 = f(LEFT0 ^ y0 ^ k1);
    int y2 = f(LEFT0 ^ RIGHT0 ^ y1 ^ k2);
    int operand3 = extract_nth_bit(f(LEFT0 ^ y0 ^ y2 ^ key), 15);

    return operand1 ^ operand2 ^ operand3;
}

int test_k_3_against_equation_2(int wordIndex, int k0, int k1, int k2, int k3)
{
    seperate_left_and_right_L_R(wordIndex);

    // operand1 = S13(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand1 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 13);

    // S7,15,23,31(LEFT0 ⊕ RIGHT0 ⊕ LEFT4)
    int operand2 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 7) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 15) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 23) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 31);

    // S7,15,23,31 F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1) ⊕ K2) ⊕ K3)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int y1 = f(LEFT0 ^ y0 ^ k1);
    int y2 = f(LEFT0 ^ RIGHT0 ^ y1 ^ k2);
    int y3 = f(LEFT0 ^ y0 ^ y2 ^ k3);
    int operand3 = extract_nth_bit(y3, 7) ^ extract_nth_bit(y3, 15) ^ extract_nth_bit(y3, 23) ^ extract_nth_bit(y3, 31);

    return operand1 ^ operand2 ^ operand3;
}

void launch_attack_on_key_3(int possible_key_0, int possible_key_1, int possible_key_2)
{

    int reduced_key_permutations_1;
    int reduced_key_permutations_2;
    int word_idx_1;
    int word_idx_2;

    for (int reduced_key_permutations_1 = 0; reduced_key_permutations_1 < OUTER_SEARCH; reduced_key_permutations_1++)
    {
        int reduced_key_prime = twelve_bit_key(reduced_key_permutations_1);
        int constant_1 = test_k_3_against_equation_1(0, reduced_key_prime, possible_key_0, possible_key_1, possible_key_2);

        for (int word_idx_1 = 1; word_idx_1 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_1++)
        {
            if (constant_1 != test_k_3_against_equation_1(word_idx_1, reduced_key_prime, possible_key_0, possible_key_1, possible_key_2))
                break;

            if (word_idx_1 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
            {
                for (int reduced_key_permutations_2 = 0; reduced_key_permutations_2 < INNER_SEARCH; reduced_key_permutations_2++)
                {
                    int expanded_key_prime = permute_twenty_bits_with_k_prime(reduced_key_permutations_2, reduced_key_prime);
                    int constant_2 = test_k_3_against_equation_2(0, possible_key_0, possible_key_1, possible_key_2, expanded_key_prime);

                    for (int word_idx_2 = 1; word_idx_2 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_2++)
                    {
                        if (constant_2 != test_k_3_against_equation_2(word_idx_2, possible_key_0, possible_key_1, possible_key_2, expanded_key_prime))
                            break;

                        if (word_idx_2 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
                            generate_K_4_K_5_and_matching_sets_of_keys(possible_key_0, possible_key_1, possible_key_2, expanded_key_prime);
                    }
                }
            }
        }
    }
}

int test_k_2_against_equation_1(int wordIndex, int key, int k0, int k1)
{
    seperate_left_and_right_L_R(wordIndex);

    // S5,13,21(LEFT0 ⊕ R0⊕ LEFT4)
    int operand1 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 5) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 13) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 21);

    // S15 F(LEFT0 ⊕ RIGHT0 ⊕ F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1) ⊕ K2)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int y1 = f(LEFT0 ^ y0 ^ k1);
    int operand2 = extract_nth_bit(f(LEFT0 ^ RIGHT0 ^ y1 ^ key), 15);

    return operand1 ^ operand2;
}

int test_k_2_against_equation_2(int wordIndex, int k0, int k1, int k2)
{
    seperate_left_and_right_L_R(wordIndex);

    // S13(LEFT0 ⊕ RIGHT0 ⊕ LEFT4)
    int operand1 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 13);

    // S7,15,23,31 F(LEFT0 ⊕ RIGHT0 ⊕ F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1) ⊕ K2)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int y1 = f(LEFT0 ^ y0 ^ k1);
    int y2 = f(LEFT0 ^ RIGHT0 ^ y1 ^ k2);
    int operand2 = extract_nth_bit(y2, 7) ^ extract_nth_bit(y2, 15) ^ extract_nth_bit(y2, 23) ^ extract_nth_bit(y2, 31);

    return operand1 ^ operand2;
}

void launch_attack_on_key_2(int possible_key_1, int possible_key_2)
{

    int reduced_key_permutations_1;
    int reduced_key_permutations_2;
    int word_idx_1;
    int word_idx_2;
    int ctr = 0;
    for (int reduced_key_permutations_1 = 0; reduced_key_permutations_1 < OUTER_SEARCH; reduced_key_permutations_1++)
    {
        int reduced_key_prime = twelve_bit_key(reduced_key_permutations_1);
        int constant_1 = test_k_2_against_equation_1(0, reduced_key_prime, possible_key_1, possible_key_2);

        for (int word_idx_1 = 1; word_idx_1 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_1++)
        {
            if (constant_1 != test_k_2_against_equation_1(word_idx_1, reduced_key_prime, possible_key_1, possible_key_2))
                break;

            if (word_idx_1 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
            {
                for (int reduced_key_permutations_2 = 0; reduced_key_permutations_2 < INNER_SEARCH; reduced_key_permutations_2++)
                {
                    int expanded_key_prime = permute_twenty_bits_with_k_prime(reduced_key_permutations_2, reduced_key_prime);
                    int constant_2 = test_k_2_against_equation_2(0, possible_key_1, possible_key_2, expanded_key_prime);

                    for (int word_idx_2 = 1; word_idx_2 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_2++)
                    {
                        if (constant_2 != test_k_2_against_equation_2(word_idx_2, possible_key_1, possible_key_2, expanded_key_prime))
                            break;

                        if (word_idx_2 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
                            launch_attack_on_key_3(possible_key_1, possible_key_2, expanded_key_prime);
                    }
                }
            }
        }
    }
}

int test_k_1_against_equation_1(int wordIndex, int key, int k0)
{
    seperate_left_and_right_L_R(wordIndex);

    // S5,13,21(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand1 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 5) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 13) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 21);

    // S15 F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int operand2 = extract_nth_bit(f(LEFT0 ^ y0 ^ key), 15);

    return operand1 ^ operand2;
}

int test_k_1_against_equation_2(int wordIndex, int k0, int k1)
{
    seperate_left_and_right_L_R(wordIndex);

    // S13(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand1 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 13);

    // S7,15,23,31 F(LEFT0 ⊕ F(LEFT0 ⊕ RIGHT0 ⊕ K0) ⊕ K1)
    int y0 = f(LEFT0 ^ RIGHT0 ^ k0);
    int y1 = f(LEFT0 ^ y0 ^ k1);
    int operand2 = extract_nth_bit(y1, 7) ^ extract_nth_bit(y1, 15) ^ extract_nth_bit(y1, 23) ^ extract_nth_bit(y1, 31);

    return operand1 ^ operand2;
}

void launch_attack_on_key_1(int possible_key_1)
{
    int reduced_key_permutations_1;
    int reduced_key_permutations_2;
    int word_idx_1;
    int word_idx_2;
    int ctr = 0;

    for (int reduced_key_permutations_1 = 0; reduced_key_permutations_1 < OUTER_SEARCH; reduced_key_permutations_1++)
    {
        int reduced_key_prime = twelve_bit_key(reduced_key_permutations_1);
        int constant_1 = test_k_1_against_equation_1(0, reduced_key_prime, possible_key_1);

        for (int word_idx_1 = 1; word_idx_1 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_1++)
        {
            if (constant_1 != test_k_1_against_equation_1(word_idx_1, reduced_key_prime, possible_key_1))
                break;

            if (word_idx_1 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
            {
                for (int reduced_key_permutations_2 = 0; reduced_key_permutations_2 < INNER_SEARCH; reduced_key_permutations_2++)
                {
                    int expanded_key_prime = permute_twenty_bits_with_k_prime(reduced_key_permutations_2, reduced_key_prime);
                    int conatant_2 = test_k_1_against_equation_2(0, possible_key_1, expanded_key_prime);

                    for (int word_idx_2 = 1; word_idx_2 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_2++)
                    {
                        if (conatant_2 != test_k_1_against_equation_2(word_idx_2, possible_key_1, expanded_key_prime))
                            break;

                        if (word_idx_2 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
                            launch_attack_on_key_2(possible_key_1, expanded_key_prime);
                    }
                }
            }
        }
    }
}

int test_k_0_against_equation_1(int wordIndex, int key)
{
    seperate_left_and_right_L_R(wordIndex);

    // S5,13,21(LEFT0 ⊕ RIGHT0 ⊕ LEFT4)
    int operand1 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 5) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 13) ^ extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 21);

    // S15(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand2 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 15);

    // S15 F(LEFT0 ⊕ RIGHT0 ⊕ K0)
    int operand3 = extract_nth_bit(f(LEFT0 ^ RIGHT0 ^ key), 15);

    return operand1 ^ operand2 ^ operand3;
}

int test_k_0_against_equation_2(int wordIndex, int key)
{
    seperate_left_and_right_L_R(wordIndex);

    // S13(LEFT0 ⊕ RIGHT0 ⊕ LEFT4)
    int operand1 = extract_nth_bit(LEFT0 ^ RIGHT0 ^ LEFT4, 13);

    // S7,15,23,31(LEFT0 ⊕ LEFT4 ⊕ RIGHT4)
    int operand2 = extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 7) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 15) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 23) ^ extract_nth_bit(LEFT0 ^ LEFT4 ^ RIGHT4, 31);

    // S7,15,23,31 F(LEFT0 ⊕ RIGHT0 ⊕ K0)
    int y0 = f(LEFT0 ^ RIGHT0 ^ key);
    int operand3 = extract_nth_bit(y0, 7) ^ extract_nth_bit(y0, 15) ^ extract_nth_bit(y0, 23) ^ extract_nth_bit(y0, 31);

    return operand1 ^ operand2 ^ operand3;
}

int main(int argc, char **argv)
{
    BYTE data[8];

    argc--;
    argv++;
    int reduced_key_permutations_1;
    int reduced_key_permutations_2;
    int word_idx_1;
    int word_idx_2;
    int ctr = 0;

    time(&start_time);
    read_plaintext_ciphertext_pairs_from_file();

    for (reduced_key_permutations_1 = 0; reduced_key_permutations_1 < OUTER_SEARCH; reduced_key_permutations_1++)
    {
        int reduced_key_prime = twelve_bit_key(reduced_key_permutations_1);
        // printf("%d\n", reduced_key_prime);
        int constant_1 = test_k_0_against_equation_1(0, reduced_key_prime);
        // printf("%d", constant_1);
        for (int word_idx_1 = 1; word_idx_1 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_1++)
        {
            if (constant_1 != test_k_0_against_equation_1(word_idx_1, reduced_key_prime))
            {
                ctr++;
                break;
            }
            if (word_idx_1 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
            {
                // printf("%u\n", reduced_key_prime);
                for (int reduced_key_permutations_2 = 0; reduced_key_permutations_2 < INNER_SEARCH; reduced_key_permutations_2++)
                {
                    int expanded_key_prime = permute_twenty_bits_with_k_prime(reduced_key_permutations_2, reduced_key_prime);
                    // printf("%u", expanded_key_prime);
                    int constant_2 = test_k_0_against_equation_2(0, expanded_key_prime);

                    for (int word_idx_2 = 1; word_idx_2 < PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT; word_idx_2++)
                    {
                        if (constant_2 != test_k_0_against_equation_2(word_idx_2, expanded_key_prime))
                            break;

                        if (word_idx_2 == PLAIN_TEXT_CIPHER_TEXT_PAIR_COUNT - 1)
                            launch_attack_on_key_1(expanded_key_prime);
                    }
                }
            }
        }
    }

    time(&end_time);

    printf("Total key combinations found: %d\n", TOTAL_KEYS_FOUND);
    printf("Time taken to find all key combinations((K0...K5)): %.2f seconds\n", difftime(end_time, start_time));

    if (argc != 8)
    {
        printf("command line error - input 8 bytes of plaintext in hex\n");
        printf("For example:-\n");
        printf("feal 01 23 45 67 89 ab cd ef\n");
        return 0;
    }
    for (int i = 0; i < 8; i++)
        sscanf(argv[i], "%hhx", &data[i]);

    printf("Plaintext=  ");
    for (int i = 0; i < 8; i++)
        printf("%02x", data[i]);
    printf("\n");

    encrypt(data, key);
    printf("Ciphertext= ");
    for (int i = 0; i < 8; i++)
        printf("%02x", data[i]);

    printf("\n");

    decrypt(data, key);
    printf("Plaintext=  ");
    for (int i = 0; i < 8; i++)
        printf("%02x", data[i]);
    printf("\n");

    return 0;
}