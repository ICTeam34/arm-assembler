#ifndef HEADER_COMMON
#define HEADER_COMMON

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include "opcodes.h"

//-OPCODES-----------------//
#define OP_AND 0x0
#define OP_EOR 0x1
#define OP_SUB 0x2
#define OP_RSB 0x3
#define OP_ADD 0x4
#define OP_TST 0x8
#define OP_TEQ 0x9
#define OP_CMP 0xA
#define OP_ORR 0xC
#define OP_MOV 0xD

//-SPECIAL-REGS------------//
#define REG_SP 13
#define REG_LR 14
#define REG_PC 15

//-CONDITION-CODES---------//
#define COND_EQ 0x0
#define COND_NE 0x1
#define COND_CS 0x2
#define COND_CC 0x3
#define COND_MI 0x4
#define COND_PL 0x5
#define COND_VS 0x6
#define COND_VC 0x7
#define COND_HI 0x8
#define COND_LS 0x9
#define COND_GE 0xA
#define COND_LT 0xB
#define COND_GT 0xC
#define COND_LE 0xD
#define COND_AL 0xE

//-SHIFT-CODES-------------//
#define SHFT_LSL 0
#define SHFT_LSR 1
#define SHFT_ASR 2
#define SHFT_ROR 3

//-MAGIC-NUMBERS-----------//
#define MULT_MAGIC      0x9
#define BRANCH_MAGIC    0x5
#define SDT_MAGIC       0x1
#define BDT_MAGIC       0x4
#define NUM_MNEMS       37
#define MAX_OPERAND_C   4
#define BX_MAGIC        0x12FFF1

#endif
