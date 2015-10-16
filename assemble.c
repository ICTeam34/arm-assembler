#include "assemble.h"

// -GLOBALS------------------------------------------------------------------//
// Number of lines in the input file
long line_c;
// Number of instructions
// instr_c always points to the first empty line in the binary
long instr_c;
// Symbol table for constants and labels
symbol_item * label_table_root = NULL;
symbol_item * const_table_root = NULL;
// Array of instructions
uint32_t* binary;
// Mapping of mnemonics to functions
mnem_func * func_map;
// --------------------------------------------------------------------------//

int main(int argc, char** argv) {
  if (argc != 3) {
    fprintf(stderr, "Usage: assemble <source> <dest> \n");
    exit(EXIT_FAILURE);
  }

  init();

  FILE* in_fp  = fopen(argv[1], "r");
  FILE* out_fp = fopen(argv[2], "w");

  if (in_fp == NULL) {
    fprintf(stderr, "Something went wrong while opening \"%s\".\n", argv[1]);
    exit(EXIT_FAILURE);
  }

  if (out_fp == NULL) {
    fprintf(stderr, "Something went wrong while opening \"%s\".\n", argv[2]);
    exit(EXIT_FAILURE);
  }

  char input_line[512];

  // count maximum number of 32-bit ints (binary instructions) to be allocated:
  //   the number of binary instructions is <= number of non-empty lines of
  //   the input file + number of ldr instructions using constants
  // POST: line_c = number of empty lines + numer of lines containing '='
  // (explained below)
  bool prev_newline = false;
  while (!feof(in_fp)) {
    char c = (char) fgetc(in_fp);
    if (c == '\n') { 
      if (!prev_newline) {
        line_c++;
      }
      prev_newline = true;
    } else {
      prev_newline = false;
      // 'ldr constant' instructions might need a directly filled memory 
      // locations.
      if (c == '=') { 
        line_c++;
      }
    }
  }


  // Go back to the beginning of the file
  rewind(in_fp);

  // Allocate memory for output
  binary = calloc((size_t) line_c, sizeof(uint32_t));
  if (binary == NULL) {
    fprintf(stderr, "calloc failure");
    exit(EXIT_FAILURE);
  }

  // Assemble line by line
  while (!feof(in_fp)) {
    // read a line and make sure it was successful
    if (fgets(input_line, 512, in_fp) != NULL) {
      assemble(input_line);
    }
  }

  // Write constants to binary
  write_constants(const_table_root);

  // print output to destination
  long output_length = instr_c;

  for (long i = 0; i < output_length; i++) {
    fwrite(&binary[i], sizeof(uint32_t), 1, out_fp);
  } 

  fclose(in_fp);
  fclose(out_fp);

  cleanup();
  return EXIT_SUCCESS;
}

//TODO: instruction suffix?
void init() {
  // Map mnemonics to their respective functions and operand count
  func_map = malloc(NUM_MNEMS * sizeof(mnem_func));
  if (func_map == NULL) {
    fprintf(stderr, "malloc failure");
    exit(EXIT_FAILURE);
  }
  func_map[0]  = (mnem_func) {"add",   3, &add};
  func_map[1]  = (mnem_func) {"sub",   3, &sub};
  func_map[2]  = (mnem_func) {"rsb",   3, &rsb};
  func_map[3]  = (mnem_func) {"and",   3, &and};
  func_map[4]  = (mnem_func) {"eor",   3, &eor};
  func_map[5]  = (mnem_func) {"orr",   3, &orr};
  func_map[6]  = (mnem_func) {"mov",   2, &mov};
  func_map[7]  = (mnem_func) {"tst",   2, &tst};
  func_map[8]  = (mnem_func) {"teq",   2, &teq};
  func_map[9]  = (mnem_func) {"cmp",   2, &cmp};
  func_map[10] = (mnem_func) {"mul",   3, &mul};
  func_map[11] = (mnem_func) {"mla",   4, &mla};
  func_map[12] = (mnem_func) {"ldr",   2, &ldr};
  func_map[13] = (mnem_func) {"str",   2, &str};
  func_map[14] = (mnem_func) {"b",     1, &b};
  func_map[15] = (mnem_func) {"lsl",   2, &lsl};
  // TODO: 1. dedicated suffix function to extract suffix?
  //       2. '^' determines if it's a stack not the other suffixes(IB,DA...) which are ignored
  func_map[16] = (mnem_func) {"ldmed",   2, &ldmed};
  func_map[17] = (mnem_func) {"ldmfd",   2, &ldmfd};
  func_map[18] = (mnem_func) {"ldmea",   2, &ldmea};
  func_map[19] = (mnem_func) {"ldmfa",   2, &ldmfa};
  func_map[20] = (mnem_func) {"stmfa",   2, &stmfa};
  func_map[21] = (mnem_func) {"stmea",   2, &stmea};
  func_map[22] = (mnem_func) {"stmfd",   2, &stmfd};
  func_map[23] = (mnem_func) {"stmed",   2, &stmed};
  func_map[24] = (mnem_func) {"ldmib",   2, &ldmed};
  func_map[25] = (mnem_func) {"ldmia",   2, &ldmfd};
  func_map[26] = (mnem_func) {"ldmdb",   2, &ldmea};
  func_map[27] = (mnem_func) {"ldmda",   2, &ldmfa};
  func_map[28] = (mnem_func) {"stmib",   2, &stmfa};
  func_map[29] = (mnem_func) {"stmia",   2, &stmea};
  func_map[30] = (mnem_func) {"stmdb",   2, &stmfd};
  func_map[31] = (mnem_func) {"stmda",   2, &stmed};
  func_map[32] = (mnem_func) {"push",    1, &push};
  func_map[33] = (mnem_func) {"pop",     1, &pop};
  func_map[34] = (mnem_func) {"pop",     1, &pop};
  func_map[35] = (mnem_func) {"bx",      1, &bx};
  func_map[36] = (mnem_func) {"bl",      1, &bl};
  line_c  = 1; // the last line might NOT end with '/n' (but EOF)
  instr_c = 0;
}

void cleanup() {
  free(binary);
  free_list(label_table_root);
  free_list(const_table_root);
  free(func_map);
}

void write_constants(symbol_item * curr_node) {
  if (curr_node == NULL) return;
  binary[instr_c] = curr_node->val.const_val;
  declared_constant(curr_node, instr_c);
  ++instr_c;
  write_constants(curr_node->next);
}

/**
 * Builds an array of assembly instructions (32-bit)
 * sets instr_c to the number of instructions of the input.
 */
void assemble(char* input_line) {
  if (input_line == NULL
        || input_line[0] == '\n' 
        || input_line[0] == ';') return;

  // get code /chop off comments/
  char* code = strtok(input_line, ";");
  char* first_token = strtok(code, ", \n");
  if (first_token == NULL || code == NULL) {
    // Nothing found
    return;
  }

  char* last_c = &first_token[strlen(first_token) - 1];
  if (*last_c == ':') {
    // Label found
    symbol_key value;
    // Get rid of the ':' character
    *last_c = '\0';
    value.label = first_token;
    found_label(LABEL, value, instr_c);

    assemble(strtok(NULL, "\n"));
  } else {
    char* cond_string = split_condition(first_token);
    uint8_t condition = parse_condition(cond_string);
    free(cond_string);

    mnem_func * map = get_function(first_token);
    if (map == NULL) {
      printf("unkown mnem: %s\n", input_line);
      return;
    }

    // We found a mapping, invoke function corresponding to
    // the mnemonic opcode, with arguments
    char* ops[MAX_OPERAND_C]; // Allocate array for max number of operands
    int i = 0;
    for (i = 0; i < map->operands - 1; i++) {
      // Only tokenize the number of operands of the instruction
      ops[i] = strtok(NULL, ", ");
    }

    ops[i] = strtok(NULL, "\n"); // chuck the rest in the last one
    while (*ops[i] == ' ') {
      //delete spaces from the string
      ++ops[i];
    }
    
    // Pass the operands to the functon pointer.
    // The rendundant ones will be disregarded by the callee
    uint32_t instr = map->functionPtr(ops[0], ops[1], ops[2], ops[3], ops[4]);
    uint32_t cond_instr = set_condition(condition, instr);
    binary[instr_c]  = cond_instr;
    
    // Increment instruction count _after_ the value is written
    // to the file
    ++instr_c;
  }
}

mnem_func *get_function(char *mnem) {
  for (int i = 0; i < NUM_MNEMS; i++) {
    bool diff = (bool) strcmp(func_map[i].mnemonic, mnem);
    if (!diff) {
      return &func_map[i];
    }
  }
  return NULL;
}

/**
* Returns the pointer to the symbol_item which was either found
* or newly inserted to the list
*/
symbol_item * add_entry(table_type t, symbol_key value, long pos) {
  symbol_item * current_node;

  symbol_key insert_val;
  if (t == CONST) {
    current_node = const_table_root;
    insert_val.const_val = value.const_val;
  } else {
    current_node = label_table_root;
    // Copy the label
    insert_val.label = malloc((strlen(value.label) + 1) * sizeof(char));
    if (insert_val.label == NULL) {
      fprintf(stderr, "malloc failure");
      exit(EXIT_FAILURE);
    }
    strcpy(insert_val.label, value.label);
  }


  symbol_item * next = current_node;

  while (next != NULL) {
    current_node = next;
    next = current_node->next;

    bool equal;
    if (t == CONST) {
      equal = current_node->val.const_val == value.const_val;
    } else {
      equal = 0 == strcmp(current_node->val.label, value.label);
    }

    if (equal) {
      if (!current_node->found) {
        insert_addr(current_node, pos);
      }
      return current_node;
    }
  }

  symbol_item* new_node = malloc(sizeof(symbol_item));
  if (new_node == NULL) {
    fprintf(stderr, "malloc failure");
    exit(EXIT_FAILURE);
  }
  new_node->val = insert_val;
  new_node->next = NULL;
  new_node->found = false;
  new_node->first_addr = NULL;
  insert_addr(new_node, pos);

  if (current_node == NULL) {
    if (t == CONST) {
      const_table_root = new_node;
    } else {
      label_table_root = new_node;
    }
  } else {
    current_node->next = new_node;
  }

  return new_node;
}

/**
 * Insert address to symbol_item (constant or label)
 */
void insert_addr(symbol_item * n, long pos) {
  if (pos < 0) {
    return; 
  }

  // Create new symbol_item
  addr_node* new_node = malloc(sizeof(addr_node));
  if (new_node == NULL) {
    fprintf(stderr, "malloc failure");
    exit(EXIT_FAILURE);
  }
  new_node->instr_pos = pos;
  new_node->next = NULL;

  // Get list root
  addr_node* current_node = n->first_addr;


  // If the root is null, make the new symbol_item the root
  if (current_node == NULL) {
    n->first_addr = new_node;
    return; 
  }

  // Otherwise, find the end
  while (current_node->next != NULL) {
    current_node = current_node->next; 
  }

  // And insert after it
  current_node->next = new_node;
}

void free_addr_list(addr_node* node) {
  if (node == NULL) return;
  free_addr_list(node->next);
  free(node);
}

void free_list(symbol_item* node) {
  if (node == NULL) return;
  free_list(node->next);
  free_addr_list(node->first_addr);
  free(node);
}

/**
 * Store the mapping of a (newly found) label to its address addr.
 * Then trace back the list of the addresses where the label is used 
 * (forward referencing) and replace the default offset (0) with the
 * calculated offset.
 * 
 * table_type t: specifies the type of the lookup table (LABEL/CONST)
 * node_val v  : contains the name(char*) of the label
 * long addr   : specifies the definition address of the label
 */
void found_label(table_type t, symbol_key v, long addr) {
  symbol_item * list_elem = add_entry(t, v, -1);
  if (list_elem->found) {
    printf("Double declaration of label ERROR\n");
  }
  list_elem->found = true;
  list_elem->def_addr = addr;

  addr_node* next_addr = list_elem->first_addr;
  while (next_addr != NULL){
    long curr_pos = next_addr->instr_pos;
    uint32_t offset = calculate_offset(addr, curr_pos);
    binary[curr_pos] |= offset;
    next_addr = next_addr->next;
  }

  free_addr_list(list_elem->first_addr);
  list_elem->first_addr = NULL;
}

/**
 * Invoked when the constant is declared at the end of the file.
 * Goes back to all the references and replaces them.
 */
void declared_constant(symbol_item *const_node, long addr) {
  // Go through the references and replace them with the offset
  addr_node* next_addr = const_node->first_addr;
  while (next_addr != NULL) {
    long curr_pos = next_addr->instr_pos;
    uint32_t offset = calculate_offset(addr, curr_pos);
    // Multiply offset by 4, to get the word address
    offset <<= 2;
    char arg[20];
    // Create ldr r0,[r15,#offset]
    sprintf(arg, "[r15,#%d]", offset);
    // Bitwise or, so that the original destination register is kept
    binary[curr_pos] |= ldr("r0", arg);
    next_addr = next_addr->next;
  }
  // No need to store the addresses anymore
  free_addr_list(const_node->first_addr);
  const_node->first_addr = NULL;
}

/**
 * Calculate offset between target position and current position
 * Take into account the effect of PC being 8 bytes ahead of the current
 * instruction in the pipeline.
 * NB: the instructions are 32-bit long instead of 8-bit long in the output
 * thus no shifting 
 */
uint32_t calculate_offset(long trgt_pos, long curr_pos){
  uint32_t offset = (uint32_t) (trgt_pos - curr_pos - 2);
  return get_bits(offset, 0, 23);
}


/**
 * Attempts to generate an immediate 12 bit operand
 * from the number.
 *
 * Returns a 12 bit number:
 * Bits 0-7 are the immediate value, unsigned. (8 bits)
 * Bits 8-11 are desribing the type and offset of 
 * the shift that is to be applied to the number.
 *
 * Prints an error if the number can't be represented in such way.
 */ 
uint16_t convert_to_immediate(uint32_t num) {

  // As a first step, we check if a rotation is needed at all.
  // It is necessary, because there are multiple solutions to
  // a single number (when the least significant bits are 0s).
  // NOTE: The other solution would be to test in the
  // empty_middle offset calculation if the offset is greater than 16.
  // In this case:
  // [offset = 32 - (offset - 16);] instead of [offset = 16 - offset;]
  if (num == (uint8_t) num) {
    // No shift needed
    return (uint16_t) num;
  }
  
  // Check if the number's middle bits are zeros
  bool empty_middle = get_bits(num, 12, 18) == 0;

  if (empty_middle) {
    // If the middle is empty, flip the 2MSBs with the 2LSBs
    uint32_t flipped = (uint16_t) num;
    flipped <<= 16;
    num >>= 16;
    flipped |= num;
    num = flipped;
  }

  uint8_t offset;

  for (offset = 0; offset < 32; offset++) {
    if (get_bit(num, 0)) {
      break; 
    }
    num >>= 1;
  }


  if (empty_middle) {
    // The original half-word flipping is already a 16-bit rotate-right
    offset = 16 - offset;
  } else {
    offset = 32 - offset; 
  }

  if (offset % 2 == 1) {
    ++offset; 
    num <<=1;
  }

  if (num != (uint8_t) num) {
    // 8 bit overflow 
    printf("Unrepresentable number\n");
    return 0;
  }

  offset >>= 1; // Div offset by two, as per the specification
  return get_bits(num | (offset << 8), 0, 11); //failure when input 0x100
}

/**
 * Get a single bit of a number
 */
bool get_bit(uint32_t number, uint8_t bit) {
  return (bool) (number & (1 << bit));
}

/**
 * Get the bits of the number between the specified start and end positions
 */
uint32_t get_bits(uint32_t number, uint8_t start, uint8_t end) {
  assert(start >= 0);
  assert(32 >= end);

  if (start > end) {
    return 0; 
  }

  uint32_t mask = (uint32_t) (~0);
  mask >>= 31 + start - end;
  number >>= start;

  return number & mask;
}

uint8_t parse_reg(char* string) {
  char* ptr = string;
  if (strcmp(string, "sp") == 0){
    return (uint8_t) REG_SP;
  }
  if (strcmp(string, "lr") == 0){
    return (uint8_t) REG_LR;
  }
  if (strcmp(string, "pc") == 0){
    return (uint8_t) REG_PC;
  }
  if (ptr[0] != 'r' || ptr[1] == '\0') {
    return -1;
  } 

  ++ptr; //removes first character ('r')
  return (uint8_t) atoi(ptr);
}

uint8_t parse_shift(char* string) {
  if (strcmp(string, "lsl") == 0) {
    return SHFT_LSL; 
  }

  if (strcmp(string, "lsr") == 0) {
    return SHFT_LSR; 
  }

  if (strcmp(string, "ror") == 0) {
    return SHFT_ROR; 
  }

  if (strcmp(string, "asr") == 0) {
    return SHFT_ASR; 
  }

  return 0;
}

/**
 * Parse string to number, optionally starting with #
 * If the number is in hexadecimal, it is converted to decimal
 */
uint32_t string_to_num(char* string) {
  char* ptr = string;
  if (*ptr == '#') {
    ++ptr; // Chop off #
  }
  return (uint32_t) (strtol(ptr, NULL, 0));
}

/**
 * Converts string into the appropriate bit pattern
 * for operand2 in the data store instruction.
 * Also sets the I flag, if the operand is an immediate value.
 */
uint32_t parse_proc_op2(char* string) {
  char* ptr = string;
  uint32_t result = 0;
  if (*ptr == '#') {
    // Immediate value 
    result |= (uint32_t) 1 << 25;
    result |= convert_to_immediate(string_to_num(string));
    return result;
  }

  // (Possibly shifted) register 
  char* firstcomma = strchr(ptr, ',');
  if (firstcomma == NULL) {
    // non shifted register
    return (uint32_t) parse_reg(ptr);
  } else {
    // shifted reg
    result = (uint32_t) parse_reg(strtok(ptr, ", "));
    uint8_t shift_type = parse_shift(strtok(NULL, " "));
    char* rest = strtok(NULL, ";"); //; is guaranteed to not be in the ptr

    if (*rest == 'r') {
      // shift by register
      uint8_t reg_shift = parse_reg(rest);
      result |= (uint32_t) reg_shift << 8;
      result |= (uint32_t) 1 << 4;
    } else {
      // shift by constant 
      uint8_t shift_offset = (uint8_t) string_to_num(rest);
      result |= (uint32_t) shift_offset << 7;
    }
    result |= (uint32_t) shift_type << 5;
    return result;
  }

  return 0;
}

uint32_t proc_store(uint8_t opcode, char* r_d, char* r_n, char* op2) {
  // parse_proc_op also sets the I flag...
  uint32_t result = parse_proc_op2(op2);
  op_data_proc_t* t = (op_data_proc_t *) &result;

  t->opcode = (uint32_t) opcode;
  t->r_n = parse_reg(r_n);
  t->r_d = parse_reg(r_d);

  return result;
}

uint32_t add(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_ADD, r_d, r_n, op2);
}

uint32_t sub(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_SUB, r_d, r_n, op2);
}

uint32_t rsb(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_RSB, r_d, r_n, op2);
}

uint32_t and(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_AND, r_d, r_n, op2);
}

uint32_t eor(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_EOR, r_d, r_n, op2);
}

uint32_t orr(char* r_d, char* r_n, char* op2) {
  return proc_store(OP_ORR, r_d, r_n, op2);
}

uint32_t mov(char* r_d, char* op2) {
  return proc_store(OP_MOV, r_d, "r0", op2);
}

uint32_t tst(char* r_n, char* op2) {
  return 1 << 20 | proc_store(OP_TST, "r0", r_n, op2);
}

uint32_t teq(char* r_n, char* op2) {
  return 1 << 20 | proc_store(OP_TEQ, "r0", r_n, op2);
}

uint32_t cmp(char* r_n, char* op2) {
  return 1 << 20 | proc_store(OP_CMP, "r0", r_n, op2);
}

uint32_t mul(char* r_d, char* r_m, char* r_s) {
  uint32_t result;
  op_mult_t* m = (op_mult_t *) &result;
  m->r_d   = parse_reg(r_d);
  m->r_s   = parse_reg(r_s);
  m->magic = MULT_MAGIC;
  m->r_m   = parse_reg(r_m);
  return result;   
}

uint32_t mla(char* r_d, char* r_m, char* r_s, char* r_n) {
  uint32_t result;
  op_mult_t* m = (op_mult_t *) &result;
  m->r_d   = parse_reg(r_d);
  m->r_s   = parse_reg(r_s);
  m->r_n   = parse_reg(r_n);
  m->magic = MULT_MAGIC;
  m->r_m   = parse_reg(r_m);
  m->a     = 1;
  return result;   
}


// <ldr/str> Rd, <address>
uint32_t ldr(char* r_d, char* op2) {
  uint32_t result;
  result = 1 << 26; // part of all sdt instructions
  op_sdt_t* op = (op_sdt_t *) &result;

  op->l = 1;
  op->r_d = parse_reg(r_d);

  // if '<=expression>'
  if (op2[0] == '=') {
    char* startptr = &op2[1];
    long op2_num = string_to_num(startptr);

    // if op2 is <= to 0xFF then generate mov code instead
    if (op2_num <= 0xFF) {
      op2[0] = '#';
      return mov(r_d, op2); // pass them to mov, changing the leading '=' to '#'
    }

    uint32_t const_mem = (uint32_t) op2_num;
    symbol_key value;
    value.const_val = const_mem;
    add_entry(CONST, value, instr_c);

    // up bit 1 (PC+offset)
    op->u = 1;
    
    // Rn = 0
    // create constant at the end of the assembly file
    // get offset between memory locations
    // generate ldr r_d, [PC, offset]
    // this result will have to be modified so that the [PC, offset] part points
    //    to the correct memory location (it was now left to be zero)
  } else {
    result = p_addressing_mode(r_d, op2, (uint32_t) 1);
  }
  
  return result;
}

uint32_t str(char* r_d, char* op2) {
  return p_addressing_mode(r_d, op2, (uint32_t) 0);
}

/**
 * Assemble str/ldr in non-numerical addressing mode (pre indexing & post
 * indexing)
 * ls bit is set if called by ldr, cleared if called by str.
 */
uint32_t p_addressing_mode(char* r_d, char* op2, uint32_t ls) {
  uint32_t result = 0;
  op_sdt_t* res = (op_sdt_t *) &result;
  res->l = ls;
  res->i = 0;                      //default addressing mode: immediate
  res->u = 1;                      //default operation: addition
  res->magic = SDT_MAGIC;

  //TODO: what if there are spaces?
  if (op2[strlen(op2) - 1] == ']'){        //P bit
    res->p = 1;
  }  

  //get the first token of the operand op2
  char* r_n = strtok(op2, "[ ,]");
  res->r_n = (uint32_t) parse_reg(r_n);
  res->r_d = (uint32_t) parse_reg(r_d);
  uint32_t offset;
  uint32_t shift_type = 0;
                                               //get the second token of op2
  r_n = strtok(NULL, "[ ,]");
                                               //default offset: 0
  if (r_n == NULL){
    offset = 0;
  } else {
    if (r_n[1] == '-'){
      res->u = 0;
      r_n[1] = '#';
      r_n++;
    } else if (r_n[1] == '+') {
      res->u = 1;
      r_n[1] = '#';
      r_n++;
    }
    if (r_n[0] == '\n'|| r_n[0] == '#') {            // if offset is immediate
      res->i = 0;
      offset = (uint32_t) string_to_num(r_n);
    } else {                               // if offset is (shifted) register
      res->i = 1;
      offset = (uint32_t) parse_reg(r_n); // set Rm
      r_n = strtok(NULL, "[ ,]");
      if (r_n != NULL){                  // if shift amount specified
        shift_type = (uint32_t) parse_shift(r_n) << 5;
        r_n = strtok(NULL, "[ ,]");

        if (r_n[0] == '#'){             // if shift by a constant amount             
          offset |= (uint32_t) 0 << 4;
          offset |= string_to_num(r_n) << 7;
        } else {                        // if shift by a register
          offset |= (uint32_t) 1 << 4;
          uint32_t r_s = parse_reg(r_n)<<8;
          offset |= r_s;
        }
        offset |= shift_type;
      }
    }
  }

  res->offset = offset;
  return result;
}

/**
 * Chops off the condition from the mnem.
 * Returns the condition string if condition found,
 * NULL otherwise.
 */
char* split_condition(char* mnem) {
  mnem_func* map = get_function(mnem);
  if (map != NULL) {
    // Function already exists, no need to split
    return NULL;
  }
  // Get the terminal \0 of the string
  size_t length = strlen(mnem);
  if (length < 3) {
    // Conditions are at least 2 chars long
    return NULL;
  }

  char* term_char = mnem + length;
  char* last_two = term_char - 2;
  if (strcmp(last_two, "eq") == 0
      || strcmp(last_two, "ge") == 0
      || strcmp(last_two, "gt") == 0
      || strcmp(last_two, "le") == 0
      || strcmp(last_two, "ne") == 0) {
    char* cond = malloc(sizeof(char) * 3); // \0...
    if (cond == NULL) {
      fprintf(stderr, "malloc failure");
      exit(EXIT_FAILURE);
    }
    strcpy(cond, last_two);
    *last_two = '\0';
    return cond;
  }

  return NULL;
}

uint32_t set_condition(uint8_t condition, uint32_t instruction) {
  return (uint32_t) condition << 28 | instruction;
}

uint8_t parse_condition(char *string) {
  if (string == NULL) {
    return COND_AL; 
  }

  if (strcmp(string, "eq") == 0) {
    return COND_EQ; 
  }

  if (strcmp(string, "ne") == 0) {
    return COND_NE; 
  }

  if (strcmp(string, "cs") == 0) {
    return COND_CS; 
  }

  if (strcmp(string, "cc") == 0) {
    return COND_CC; 
  }

  if (strcmp(string, "mi") == 0) {
    return COND_MI; 
  }

  if (strcmp(string, "pl") == 0) {
    return COND_PL; 
  }

  if (strcmp(string, "vs") == 0) {
    return COND_VS; 
  }

  if (strcmp(string, "vc") == 0) {
    return COND_VC; 
  }

  if (strcmp(string, "hi") == 0) {
    return COND_HI; 
  }

  if (strcmp(string, "ls") == 0) {
    return COND_LS; 
  }

  if (strcmp(string, "ge") == 0) {
    return COND_GE; 
  }

  if (strcmp(string, "lt") == 0) {
    return COND_LT; 
  }

  if (strcmp(string, "gt") == 0) {
    return COND_GT; 
  }

  if (strcmp(string, "le") == 0) {
    return COND_LE; 
  }

  return COND_AL;
}

/**
 * Called upon finding the usage of a label.
 * Add the current instruction position instr_c to the address list
 * of the label.
 * If the label is defined calculate the offset; otherwise set the 
 * offset to zero.
 */
uint32_t b(char* label) {
  uint32_t result = 0;
  op_branch_t* res = (op_branch_t *) &result;
  res->magic = BRANCH_MAGIC;

  symbol_key value;
  value.label = label;
  symbol_item * node = add_entry(LABEL, value, instr_c);

  if (node->found) {
    res->offset =  calculate_offset(node->def_addr, instr_c);
  }
  return result;
}

// TODO: test
uint32_t bx(char* reg) {
  uint32_t result = 0;
  op_bx_t* inst = (op_bx_t *) &result;
  inst->r_n     = parse_reg(reg);
  return result;
}

// TODO: test
uint32_t bl(char* label) {
  uint32_t result = b(label);
  op_branch_t* res = (op_branch_t *) &result;
  res->l = 1;
  return result;
}

uint32_t lsl(char* r_d, char* expression) {
  char lsl_exp[6 + strlen(r_d) + strlen(expression)];
  strcpy(lsl_exp, r_d);
  strcpy(lsl_exp + strlen(r_d), ", lsl ");
  strcpy(lsl_exp + 6 + strlen(r_d), expression);
  return mov(r_d,lsl_exp);
}

uint32_t bdt(char* r_n, char* regs, uint32_t l, uint32_t p, uint32_t u) {
  uint32_t result = 0;
  op_bdt_t* res = (op_bdt_t *) &result;
  res->magic = BDT_MAGIC;
  res->p = p;
  res->u = u;
  res->l = l;
  res->w = (r_n[strlen(r_n) - 1] == '!');
  res->s = (regs[strlen(regs) - 1] == '^'); //TODO: exception handling

  r_n = strtok(r_n, "!");                                 // chop off '!'
  regs = strtok(regs, "^");                               // chop off '^'
  res->r_n = parse_reg(r_n);

  char* next_reg = strtok(regs, " {, }");
  uint16_t reg_bits = 0;
  uint16_t mask;

  while (next_reg != NULL) {
    if (strchr(next_reg, '-') == NULL) {                    // ...,Rn,... 
      mask = (uint16_t) 1 << parse_reg(next_reg);
    } else {                                              //...,Ra-Rb,...
      uint8_t start_reg = parse_reg(strtok(next_reg, "-"));
      uint8_t end_reg   = parse_reg(strtok(NULL, "\n"));
      if (end_reg > 15) {
        //TODO: handle some kind of error, possibly introduce some 
        // kind of halting mechanism (maybe the spec says something about it)
      }
      mask = (uint16_t) ((uint16_t) ~0 >> (15 - end_reg)) << start_reg;
   }

   reg_bits |= mask;
   next_reg = strtok (NULL, " {, ]!^");
  } 
  res->reg_bits = reg_bits;
  return result;
}

uint32_t ldmed(char* r_n, char* regs) {
  return bdt(r_n, regs, 1, 1, 1);
}

uint32_t ldmfd(char* r_n, char* regs) {
  return bdt(r_n, regs, 1, 0, 1);
}

uint32_t ldmea(char* r_n, char* regs) {
  return bdt(r_n, regs, 1, 1, 0);
}

uint32_t ldmfa(char* r_n, char* regs) {
  return bdt(r_n, regs, 1, 0, 0);
}

uint32_t stmfa(char* r_n, char* regs) {
  return bdt(r_n, regs, 0, 1, 1);
}

uint32_t stmea(char* r_n, char* regs) {
  return bdt(r_n, regs, 0, 0, 1);
}

uint32_t stmfd(char* r_n, char* regs) {
  return bdt(r_n, regs, 0, 1, 0);
}

uint32_t stmed(char* r_n, char* regs) {
  return bdt(r_n, regs, 0, 0, 0);
}

uint32_t push(char* regv) {
  char sp[4] = "sp!";
  return stmfd(sp, regv);
}

uint32_t pop(char* regv) {
  char sp[4] = "sp!";
  return ldmfd(sp, regv);
}
