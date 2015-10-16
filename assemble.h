#ifndef HEADER_ASSEMBLE
#define HEADER_ASSEMBLE 

#include "common.h"

/**
 * Line address linked list
 */
typedef struct addr_node_s {
  long instr_pos;
  struct addr_node_s *next;
} addr_node;

typedef enum {
  CONST,
  LABEL
} table_type;

typedef union {
  char* label;
  uint32_t const_val;
} symbol_key;

/**
 * [(REF_NAME, [INSTR_ADDR])]
 * Address table for mapping address references to the addresses
 * they were used at
 */
typedef struct node_s {
  symbol_key val;
  long def_addr; // address of the definition of the symbol_item val (const|label)
  bool found;
  addr_node* first_addr;
  struct node_s* next;
} symbol_item;

typedef struct {
  char* mnemonic;
  int operands;
  uint32_t (*functionPtr)();
} mnem_func;
//---------------------------------//
uint16_t convert_to_immediate(uint32_t from);
bool get_bit(uint32_t number, uint8_t bit);
uint32_t get_bits(uint32_t number, uint8_t start, uint8_t end);
void assemble(char* input_line);
symbol_item * add_entry(table_type t, symbol_key value, long pos);
void insert_addr(symbol_item * n, long pos);
void free_addr_list(addr_node* node);
void free_list(symbol_item* node);
mnem_func *get_function(char *mnem);
void found_label(table_type t, symbol_key v, long addr);
uint32_t calculate_offset(long trgt_pos, long curr_pos);
uint8_t parse_reg(char* string);
uint32_t parse_proc_op2(char* string);
uint32_t proc_store(uint8_t opcode, char* r_d, char* r_n, char* op2);

uint32_t add(char* r_d, char* r_n, char* op2);
uint32_t sub(char* r_d, char* r_n, char* op2);
uint32_t rsb(char* r_d, char* r_n, char* op2);
uint32_t and(char* r_d, char* r_n, char* op2);
uint32_t eor(char* r_d, char* r_n, char* op2);
uint32_t orr(char* r_d, char* r_n, char* op2);
uint32_t mov(char* r_d, char* op2);
uint32_t tst(char* r_n, char* op2);
uint32_t teq(char* r_n, char* op2);
uint32_t cmp(char* r_n, char* op2);
uint32_t mul(char* r_d, char* r_m, char* r_s);
uint32_t mla(char* r_d, char* r_m, char* r_s, char* r_n);

uint32_t ldr(char* r_d, char* op2);
uint32_t str(char* r_d, char* op2);
uint32_t bdt(char* r_n, char* regs, uint32_t l, uint32_t p, uint32_t u);
uint32_t ldmed(char* r_n, char* regs);
uint32_t ldmfd(char* r_n, char* regs);
uint32_t ldmea(char* r_n, char* regs);
uint32_t ldmfa(char* r_n, char* regs);
uint32_t stmfa(char* r_n, char* regs);
uint32_t stmea(char* r_n, char* regs);
uint32_t stmfd(char* r_n, char* regs);
uint32_t stmed(char* r_n, char* regs);
uint32_t push(char*);
uint32_t pop(char*);

uint32_t b(char*);
uint32_t bx(char*);
uint32_t bl(char*);

uint32_t lsl(char* r_d, char* expression);

uint32_t p_addressing_mode(char* r_d, char* op2, uint32_t ls);
uint8_t parse_condition(char *);
uint32_t set_condition(uint8_t condition, uint32_t instruction);
char* split_condition(char* mnem);
void write_constants(symbol_item * first_node);
void declared_constant(symbol_item *const_node, long addr) ;
void init();
void cleanup();
uint32_t string_to_num(char* string) ;

#endif
