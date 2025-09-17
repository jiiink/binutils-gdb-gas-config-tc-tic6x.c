/* TI C6X assembler.
   Copyright (C) 2010-2025 Free Software Foundation, Inc.
   Contributed by Joseph Myers <joseph@codesourcery.com>
   		  Bernd Schmidt  <bernds@codesourcery.com>

   This file is part of GAS, the GNU Assembler.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#include "as.h"
#include "dwarf2dbg.h"
#include "dw2gencfi.h"
#include "safe-ctype.h"
#include "subsegs.h"
#include "opcode/tic6x.h"
#include "elf/tic6x.h"
#include "elf32-tic6x.h"

/* Truncate and sign-extend at 32 bits, so that building on a 64-bit
   host gives identical results to a 32-bit host.  */
#define TRUNC(X)	((valueT) (X) & 0xffffffffU)
#define SEXT(X)		((TRUNC (X) ^ 0x80000000U) - 0x80000000U)

#define streq(a, b)           (strcmp (a, b) == 0)

/* Stuff for .scomm symbols.  */
static segT sbss_section;
static asection scom_section;
static asymbol scom_symbol;

const char comment_chars[] = ";";
const char line_comment_chars[] = "#*;";
const char line_separator_chars[] = "@";

const char EXP_CHARS[] = "eE";
const char FLT_CHARS[] = "dDfF";

const char md_shortopts[] = "";

enum
  {
    OPTION_MARCH = OPTION_MD_BASE,
    OPTION_MBIG_ENDIAN,
    OPTION_MLITTLE_ENDIAN,
    OPTION_MDSBT,
    OPTION_MNO_DSBT,
    OPTION_MPID,
    OPTION_MPIC,
    OPTION_MNO_PIC,
    OPTION_MGENERATE_REL
  };

const struct option md_longopts[] =
  {
    { "march", required_argument, NULL, OPTION_MARCH },
    { "mbig-endian", no_argument, NULL, OPTION_MBIG_ENDIAN },
    { "mlittle-endian", no_argument, NULL, OPTION_MLITTLE_ENDIAN },
    { "mdsbt", no_argument, NULL, OPTION_MDSBT },
    { "mno-dsbt", no_argument, NULL, OPTION_MNO_DSBT },
    { "mpid", required_argument, NULL, OPTION_MPID },
    { "mpic", no_argument, NULL, OPTION_MPIC },
    { "mno-pic", no_argument, NULL, OPTION_MNO_PIC },
    { "mgenerate-rel", no_argument, NULL, OPTION_MGENERATE_REL },
    { NULL, no_argument, NULL, 0 }
  };
const size_t md_longopts_size = sizeof (md_longopts);

/* The instructions enabled based only on the selected architecture
   (all instructions, if no architecture specified).  */
static unsigned short tic6x_arch_enable = (TIC6X_INSN_C62X
					   | TIC6X_INSN_C64X
					   | TIC6X_INSN_C64XP
					   | TIC6X_INSN_C67X
					   | TIC6X_INSN_C67XP
					   | TIC6X_INSN_C674X);

/* The instructions enabled based on the current set of features
   (architecture, as modified by other options).  */
static unsigned short tic6x_features;

/* The architecture attribute value, or C6XABI_Tag_ISA_none if
   not yet set.  */
static int tic6x_arch_attribute = C6XABI_Tag_ISA_none;

/* Whether any instructions at all have been seen.  Once any
   instructions have been seen, architecture attributes merge into the
   previous attribute value rather than replacing it.  */
static bool tic6x_seen_insns = false;

/* The number of registers in each register file supported by the
   current architecture.  */
static unsigned int tic6x_num_registers;

/* Whether predication on A0 is possible.  */
static bool tic6x_predicate_a0;

/* Whether execute packets can cross fetch packet boundaries.  */
static bool tic6x_can_cross_fp_boundary;

/* Whether there are constraints on simultaneous reads and writes of
   40-bit data.  */
static bool tic6x_long_data_constraints;

/* Whether compact instructions are available.  */
static bool tic6x_compact_insns;

/* Whether to generate RELA relocations.  */
static bool tic6x_generate_rela = true;

/* Whether the code uses DSBT addressing.  */
static bool tic6x_dsbt;

/* Types of position-independent data (attribute values for
   Tag_ABI_PID).  */
typedef enum
  {
    tic6x_pid_no = 0,
    tic6x_pid_near = 1,
    tic6x_pid_far = 2
  } tic6x_pid_type;

/* The type of data addressing used in this code.  */
static tic6x_pid_type tic6x_pid;

/* Whether the code uses position-independent code.  */
static bool tic6x_pic;

/* Table of supported architecture variants.  */
typedef struct
{
  const char *arch;
  int attr;
  unsigned short features;
} tic6x_arch_table;
static const tic6x_arch_table tic6x_arches[] =
  {
    { "c62x", C6XABI_Tag_ISA_C62X, TIC6X_INSN_C62X },
    { "c64x", C6XABI_Tag_ISA_C64X, TIC6X_INSN_C62X | TIC6X_INSN_C64X },
    { "c64x+", C6XABI_Tag_ISA_C64XP, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C64X
				      | TIC6X_INSN_C64XP) },
    { "c67x", C6XABI_Tag_ISA_C67X, TIC6X_INSN_C62X | TIC6X_INSN_C67X },
    { "c67x+", C6XABI_Tag_ISA_C67XP, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C67X
				      | TIC6X_INSN_C67XP) },
    { "c674x", C6XABI_Tag_ISA_C674X, (TIC6X_INSN_C62X
				      | TIC6X_INSN_C64X
				      | TIC6X_INSN_C64XP
				      | TIC6X_INSN_C67X
				      | TIC6X_INSN_C67XP
				      | TIC6X_INSN_C674X) }
  };

/* Caller saved register encodings.  The standard frame layout uses this
   order, starting from the highest address.  There must be
   TIC6X_NUM_UNWIND_REGS values.  */
enum
{
  UNWIND_A15,
  UNWIND_B15,
  UNWIND_B14,
  UNWIND_B13,
  UNWIND_B12,
  UNWIND_B11,
  UNWIND_B10,
  UNWIND_B3,
  UNWIND_A14,
  UNWIND_A13,
  UNWIND_A12,
  UNWIND_A11,
  UNWIND_A10
};

static void tic6x_output_unwinding (bool need_extab);

/* Return the frame unwind state for the current function, allocating
   as necessary.  */

static tic6x_unwind_info *tic6x_get_unwind(void)
{
    tic6x_unwind_info *unwind;
    seg_info_type *segment = seg_info(now_seg);
    
    unwind = segment->tc_segment_info_data.unwind;
    if (unwind)
        return unwind;
    
    unwind = segment->tc_segment_info_data.text_unwind;
    if (unwind)
        return unwind;
    
    unwind = XNEW(tic6x_unwind_info);
    segment->tc_segment_info_data.unwind = unwind;
    memset(unwind, 0, sizeof(*unwind));
    return unwind;
}

/* Update the selected architecture based on ARCH, giving an error if
   ARCH is an invalid value.  Does not call tic6x_update_features; the
   caller must do that if necessary.  */

static void
tic6x_use_arch (const char *arch)
{
  unsigned int i;

  for (i = 0; i < ARRAY_SIZE (tic6x_arches); i++)
    {
      if (strcmp (arch, tic6x_arches[i].arch) != 0)
        continue;
        
      tic6x_arch_enable = tic6x_arches[i].features;
      
      if (tic6x_seen_insns)
        tic6x_arch_attribute = elf32_tic6x_merge_arch_attributes (tic6x_arch_attribute,
                                                                  tic6x_arches[i].attr);
      else
        tic6x_arch_attribute = tic6x_arches[i].attr;
        
      return;
    }

  as_bad (_("unknown architecture '%s'"), arch);
}

/* Table of supported -mpid arguments.  */
typedef struct
{
  const char *arg;
  tic6x_pid_type attr;
} tic6x_pid_type_table;
static const tic6x_pid_type_table tic6x_pid_types[] =
  {
    { "no", tic6x_pid_no },
    { "near", tic6x_pid_near },
    { "far", tic6x_pid_far }
  };

/* Handle -mpid=ARG.  */

static void
tic6x_use_pid (const char *arg)
{
  unsigned int i;

  for (i = 0; i < ARRAY_SIZE (tic6x_pid_types); i++)
    if (strcmp (arg, tic6x_pid_types[i].arg) == 0)
      {
	tic6x_pid = tic6x_pid_types[i].attr;
	return;
      }

  as_bad (_("unknown -mpid= argument '%s'"), arg);
}

/* Parse a target-specific option.  */

int
md_parse_option (int c, const char *arg)
{
  switch (c)
    {
    case OPTION_MARCH:
      tic6x_use_arch (arg);
      break;

    case OPTION_MBIG_ENDIAN:
      target_big_endian = 1;
      break;

    case OPTION_MLITTLE_ENDIAN:
      target_big_endian = 0;
      break;

    case OPTION_MDSBT:
      tic6x_dsbt = 1;
      break;

    case OPTION_MNO_DSBT:
      tic6x_dsbt = 0;
      break;

    case OPTION_MPID:
      tic6x_use_pid (arg);
      break;

    case OPTION_MPIC:
      tic6x_pic = 1;
      break;

    case OPTION_MNO_PIC:
      tic6x_pic = 0;
      break;

    case OPTION_MGENERATE_REL:
      tic6x_generate_rela = false;
      break;

    default:
      return 0;
    }
  return 1;
}

void
md_show_usage (FILE *stream ATTRIBUTE_UNUSED)
{
  static const char *options[] = {
    "  -march=ARCH             enable instructions from architecture ARCH\n",
    "  -mbig-endian            generate big-endian code\n",
    "  -mlittle-endian         generate little-endian code\n",
    "  -mdsbt                  code uses DSBT addressing\n",
    "  -mno-dsbt               code does not use DSBT addressing\n",
    "  -mpid=no                code uses position-dependent data addressing\n",
    "  -mpid=near              code uses position-independent data addressing,\n"
    "                            GOT accesses use near DP addressing\n",
    "  -mpid=far               code uses position-independent data addressing,\n"
    "                            GOT accesses use far DP addressing\n",
    "  -mpic                   code addressing is position-independent\n",
    "  -mno-pic                code addressing is position-dependent\n"
  };
  
  unsigned int i;
  
  fputc ('\n', stream);
  fprintf (stream, _("TMS320C6000 options:\n"));
  
  for (i = 0; i < sizeof(options) / sizeof(options[0]); i++)
    fprintf (stream, _(options[i]));
  
  fputc ('\n', stream);
  fprintf (stream, _("Supported ARCH values are:"));
  
  for (i = 0; i < ARRAY_SIZE (tic6x_arches); i++)
    fprintf (stream, " %s", tic6x_arches[i].arch);
    
  fputc ('\n', stream);
}

/* Update enabled features based on the current architecture and
   related settings.  */
static void
tic6x_update_features (void)
{
  tic6x_features = tic6x_arch_enable;

  tic6x_num_registers
    = (tic6x_arch_enable & (TIC6X_INSN_C64X | TIC6X_INSN_C67XP)) ? 32 : 16;

  tic6x_predicate_a0 = (tic6x_arch_enable & TIC6X_INSN_C64X) != 0;

  tic6x_can_cross_fp_boundary
    = (tic6x_arch_enable & (TIC6X_INSN_C64X | TIC6X_INSN_C67XP)) != 0;

  tic6x_long_data_constraints = (tic6x_arch_enable & TIC6X_INSN_C64X) == 0;

  tic6x_compact_insns = (tic6x_arch_enable & TIC6X_INSN_C64XP) != 0;
}

/* Do configuration after all options have been parsed.  */

void tic6x_after_parse_args(void)
{
    tic6x_update_features();
}

/* Parse a .cantunwind directive.  */
static void
s_tic6x_cantunwind (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind->data_bytes == 0)
    return;

  if (unwind->data_bytes != -1)
    {
      as_bad (_("unexpected .cantunwind directive"));
      return;
    }

  demand_empty_rest_of_line ();

  if (unwind->personality_routine || unwind->personality_index != -1)
    as_bad (_("personality routine specified for cantunwind frame"));

  unwind->personality_index = -2;
}

/* Parse a .handlerdata directive.  */
static void
s_tic6x_handlerdata (int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (validate_handlerdata_preconditions(unwind))
    {
      tic6x_output_unwinding(true);
    }
}

static bool
validate_handlerdata_preconditions(tic6x_unwind_info *unwind)
{
  if (!check_saved_segment(unwind))
    return false;

  if (!check_no_duplicate_directive(unwind))
    return false;

  if (!check_personality_routine(unwind))
    return false;

  return true;
}

static bool
check_saved_segment(tic6x_unwind_info *unwind)
{
  if (!unwind->saved_seg)
    {
      as_bad (_("unexpected .handlerdata directive"));
      return false;
    }
  return true;
}

static bool
check_no_duplicate_directive(tic6x_unwind_info *unwind)
{
  if (unwind->table_entry || unwind->personality_index == -2)
    {
      as_bad (_("duplicate .handlerdata directive"));
      return false;
    }
  return true;
}

static bool
check_personality_routine(tic6x_unwind_info *unwind)
{
  if (unwind->personality_index == -1 && unwind->personality_routine == NULL)
    {
      as_bad (_("personality routine required before .handlerdata directive"));
      return false;
    }
  return true;
}

/* Parse a .endp directive.  */
static void output_exidx_if_needed(tic6x_unwind_info *unwind)
{
    if (!unwind->table_entry)
        tic6x_output_unwinding(false);
}

static void restore_text_section(tic6x_unwind_info *unwind)
{
    subseg_set(unwind->saved_seg, unwind->saved_subseg);
}

static void reset_unwind_info(tic6x_unwind_info *unwind)
{
    unwind->saved_seg = NULL;
    unwind->table_entry = NULL;
    unwind->data_bytes = 0;
}

static void s_tic6x_endp(int ignored ATTRIBUTE_UNUSED)
{
    tic6x_unwind_info *unwind = tic6x_get_unwind();

    if (unwind->data_bytes != 0)
    {
        output_exidx_if_needed(unwind);
        restore_text_section(unwind);
    }

    reset_unwind_info(unwind);
}

/* Parse a .personalityindex directive.  */
static int is_valid_personality_index(expressionS *exp)
{
  return exp->X_op == O_constant && 
         exp->X_add_number >= 0 && 
         exp->X_add_number <= 15;
}

static void check_duplicate_personality(tic6x_unwind_info *unwind)
{
  if (unwind->personality_routine || unwind->personality_index != -1)
    as_bad (_("duplicate .personalityindex directive"));
}

static void s_tic6x_personalityindex(int ignored ATTRIBUTE_UNUSED)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind();
  expressionS exp;

  check_duplicate_personality(unwind);

  expression(&exp);

  if (!is_valid_personality_index(&exp))
    {
      as_bad(_("bad personality routine number"));
      ignore_rest_of_line();
      return;
    }

  unwind->personality_index = exp.X_add_number;
  demand_empty_rest_of_line();
}

static void
s_tic6x_personality (int ignored ATTRIBUTE_UNUSED)
{
  char *name, c;
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  if (unwind->personality_routine || unwind->personality_index != -1)
    as_bad (_("duplicate .personality directive"));

  c = get_symbol_name (&name);
  unwind->personality_routine = symbol_find_or_make (name);
  (void) restore_line_pointer (c);
  demand_empty_rest_of_line ();
}

/* Parse a .arch directive.  */
static void
s_tic6x_arch (int ignored ATTRIBUTE_UNUSED)
{
  char *arch = input_line_pointer;
  char *end = find_statement_end(input_line_pointer);
  char saved_char = *end;
  
  *end = 0;
  tic6x_use_arch (arch);
  tic6x_update_features ();
  *end = saved_char;
  
  input_line_pointer = end;
  demand_empty_rest_of_line ();
}

static char *
find_statement_end (char *ptr)
{
  while (!is_end_of_stmt (*ptr) && !is_whitespace (*ptr))
    ptr++;
  return ptr;
}

/* Parse a .ehtype directive.  */

static void flush_pending_output_if_needed(void)
{
#ifdef md_flush_pending_output
    md_flush_pending_output();
#endif
}

static void align_cons_if_needed(void)
{
#ifdef md_cons_align
    md_cons_align(4);
#endif
}

static int handle_empty_statement(void)
{
    if (is_it_end_of_statement())
    {
        demand_empty_rest_of_line();
        return 1;
    }
    return 0;
}

static int validate_symbol_expression(expressionS *exp)
{
    expression(exp);
    
    if (exp->X_op != O_symbol)
    {
        as_bad(_("expected symbol"));
        return 0;
    }
    return 1;
}

static void create_ehtype_fixup(expressionS *exp)
{
    const int FIXUP_SIZE = 4;
    char *p = frag_more(FIXUP_SIZE);
    
    memset(p, 0, FIXUP_SIZE);
    fix_new_exp(frag_now, p - frag_now->fr_literal, FIXUP_SIZE,
                exp, 0, BFD_RELOC_C6000_EHTYPE);
}

static void s_tic6x_ehtype(int ignored ATTRIBUTE_UNUSED)
{
    expressionS exp;
    
    flush_pending_output_if_needed();
    
    if (handle_empty_statement())
        return;
    
    align_cons_if_needed();
    
    if (!validate_symbol_expression(&exp))
        return;
    
    create_ehtype_fixup(&exp);
    demand_empty_rest_of_line();
}

/* Parse a .nocmp directive.  */

static void
s_tic6x_nocmp (int ignored ATTRIBUTE_UNUSED)
{
  seg_info (now_seg)->tc_segment_info_data.nocmp = true;
  demand_empty_rest_of_line ();
}

/* .scomm pseudo-op handler.

   This is a new pseudo-op to handle putting objects in .scommon.
   By doing this the linker won't need to do any work,
   and more importantly it removes the implicit -G arg necessary to
   correctly link the object file.  */

static void parse_symbol_name(char **name, char *c, char **p)
{
    *c = get_symbol_name(name);
    *p = input_line_pointer;
    (void) restore_line_pointer(*c);
    SKIP_WHITESPACE();
}

static int validate_comma_after_symbol(void)
{
    if (*input_line_pointer != ',')
    {
        as_bad(_("expected comma after symbol name"));
        ignore_rest_of_line();
        return 0;
    }
    input_line_pointer++;
    return 1;
}

static int parse_size(offsetT *size)
{
    *size = get_absolute_expression();
    if (*size < 0)
    {
        as_warn(_("invalid length for .scomm directive"));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static offsetT parse_alignment(void)
{
    if (*input_line_pointer != ',')
        return 8;
    
    ++input_line_pointer;
    offsetT align = get_absolute_expression();
    if (align <= 0)
    {
        as_warn(_("alignment is not a positive number"));
        return 8;
    }
    return align;
}

static int convert_to_power_of_2(offsetT align, int *align2)
{
    *align2 = 0;
    if (!align)
        return 1;
    
    while ((align & 1) == 0)
    {
        align >>= 1;
        (*align2)++;
    }
    
    if (align != 1)
    {
        as_bad(_("alignment is not a power of 2"));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static symbolS* find_or_create_symbol(char *name, char c, char *p)
{
    *p = 0;
    symbolS *symbolP = symbol_find_or_make(name);
    *p = c;
    return symbolP;
}

static int validate_symbol_undefined(symbolS *symbolP)
{
    if (S_IS_DEFINED(symbolP))
    {
        as_bad(_("attempt to re-define symbol `%s'"), S_GET_NAME(symbolP));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static int validate_symbol_size(symbolS *symbolP, offsetT size)
{
    if (S_GET_VALUE(symbolP) && S_GET_VALUE(symbolP) != (valueT)size)
    {
        as_bad(_("attempt to redefine `%s' with a different length"), S_GET_NAME(symbolP));
        ignore_rest_of_line();
        return 0;
    }
    return 1;
}

static void setup_local_symbol(symbolS *symbolP, int align2, offsetT size)
{
    segT old_sec = now_seg;
    int old_subsec = now_subseg;
    char *pfrag;
    
    record_alignment(sbss_section, align2);
    subseg_set(sbss_section, 0);
    
    if (align2)
        frag_align(align2, 0, 0);
    
    if (S_GET_SEGMENT(symbolP) == sbss_section)
        symbol_get_frag(symbolP)->fr_symbol = 0;
    
    symbol_set_frag(symbolP, frag_now);
    pfrag = frag_var(rs_org, 1, 1, 0, symbolP, size, NULL);
    *pfrag = 0;
    
    S_SET_SIZE(symbolP, size);
    S_SET_SEGMENT(symbolP, sbss_section);
    S_CLEAR_EXTERNAL(symbolP);
    
    subseg_set(old_sec, old_subsec);
}

static void setup_external_symbol(symbolS *symbolP, int align2, offsetT size)
{
    S_SET_VALUE(symbolP, size);
    S_SET_ALIGN(symbolP, 1 << align2);
    S_SET_EXTERNAL(symbolP);
    S_SET_SEGMENT(symbolP, &scom_section);
}

static void s_tic6x_scomm(int ignore ATTRIBUTE_UNUSED)
{
    char *name;
    char c;
    char *p;
    offsetT size;
    symbolS *symbolP;
    offsetT align;
    int align2;
    
    parse_symbol_name(&name, &c, &p);
    
    if (!validate_comma_after_symbol())
        return;
    
    if (!parse_size(&size))
        return;
    
    align = parse_alignment();
    
    if (!convert_to_power_of_2(align, &align2))
        return;
    
    symbolP = find_or_create_symbol(name, c, p);
    
    if (!validate_symbol_undefined(symbolP))
        return;
    
    if (!validate_symbol_size(symbolP, size))
        return;
    
    if (symbol_get_obj(symbolP)->local)
        setup_local_symbol(symbolP, align2, size);
    else
        setup_external_symbol(symbolP, align2, size);
    
    symbol_get_bfdsym(symbolP)->flags |= BSF_OBJECT;
    demand_empty_rest_of_line();
}

/* Track for each attribute whether it has been set explicitly (and so
   should not have a default value set by the assembler).  */
static bool tic6x_attributes_set_explicitly[NUM_KNOWN_OBJ_ATTRIBUTES];

/* Parse a .c6xabi_attribute directive.  */

static void
s_tic6x_c6xabi_attribute (int ignored ATTRIBUTE_UNUSED)
{
  int tag = obj_elf_vendor_attribute (OBJ_ATTR_PROC);

  if (tag < NUM_KNOWN_OBJ_ATTRIBUTES)
    tic6x_attributes_set_explicitly[tag] = true;
}

typedef struct
{
  const char *name;
  int tag;
} tic6x_attribute_table;

static const tic6x_attribute_table tic6x_attributes[] =
  {
#define TAG(tag, value) { #tag, tag },
#include "elf/tic6x-attrs.h"
#undef TAG
  };

/* Convert an attribute name to a number.  */

int
tic6x_convert_symbolic_attribute (const char *name)
{
  unsigned int i;

  for (i = 0; i < ARRAY_SIZE (tic6x_attributes); i++)
    if (strcmp (name, tic6x_attributes[i].name) == 0)
      return tic6x_attributes[i].tag;

  return -1;
}

const pseudo_typeS md_pseudo_table[] =
  {
    { "arch", s_tic6x_arch, 0 },
    { "c6xabi_attribute", s_tic6x_c6xabi_attribute, 0 },
    { "nocmp", s_tic6x_nocmp, 0 },
    { "scomm",	s_tic6x_scomm, 0 },
    { "word", cons, 4 },
    { "ehtype", s_tic6x_ehtype, 0 },
    { "endp", s_tic6x_endp, 0 },
    { "handlerdata", s_tic6x_handlerdata, 0 },
    { "personalityindex", s_tic6x_personalityindex, 0 },
    { "personality", s_tic6x_personality, 0 },
    { "cantunwind", s_tic6x_cantunwind, 0 },
    { 0, 0, 0 }
  };

/* Hash table of opcodes.  For each opcode name, this stores a pointer
   to a tic6x_opcode_list listing (in an arbitrary order) all opcode
   table entries with that name.  */
static htab_t opcode_hash;

/* Initialize the assembler (called once at assembler startup).  */

void
md_begin (void)
{
  segT seg;
  subsegT subseg;

  bfd_set_arch_mach (stdoutput, TARGET_ARCH, 0);

  initialize_opcode_hash_table();

  seg = now_seg;
  subseg = now_subseg;

  create_sbss_section();
  
  subseg_set (seg, subseg);

  create_scommon_section();
}

static void
initialize_opcode_hash_table (void)
{
  tic6x_opcode_id id;

  opcode_hash = str_htab_create ();
  for (id = 0; id < tic6x_opcode_max; id++)
    {
      add_opcode_to_hash (id);
    }
}

static void
add_opcode_to_hash (tic6x_opcode_id id)
{
  tic6x_opcode_list *opc = XNEW (tic6x_opcode_list);

  opc->id = id;
  opc->next = str_hash_find (opcode_hash, tic6x_opcode_table[id].name);
  str_hash_insert (opcode_hash, tic6x_opcode_table[id].name, opc, 1);
}

static void
create_sbss_section (void)
{
  flagword applicable;

  sbss_section = subseg_new (".bss", 0);
  seg_info (sbss_section)->bss = 1;

  applicable = bfd_applicable_section_flags (stdoutput);
  bfd_set_section_flags (sbss_section, applicable & SEC_ALLOC);
}

static void
create_scommon_section (void)
{
  scom_section                = *bfd_com_section_ptr;
  scom_section.name           = ".scommon";
  scom_section.output_section = & scom_section;
  scom_section.symbol         = & scom_symbol;
  scom_symbol                 = * bfd_com_section_ptr->symbol;
  scom_symbol.name            = ".scommon";
  scom_symbol.section         = & scom_section;
}

/* Whether the current line being parsed had the "||" parallel bars.  */
static bool tic6x_line_parallel;

/* Whether the current line being parsed started "||^" to indicate an
   SPMASKed parallel instruction.  */
static bool tic6x_line_spmask;

/* If the current line being parsed had an instruction predicate, the
   creg value for that predicate (which must be nonzero); otherwise
   0.  */
static unsigned int tic6x_line_creg;

/* If the current line being parsed had an instruction predicate, the
   z value for that predicate; otherwise 0.  */
static unsigned int tic6x_line_z;

/* Return 1 (updating input_line_pointer as appropriate) if the line
   starting with C (immediately before input_line_pointer) starts with
   pre-opcode text appropriate for this target, 0 otherwise.  */

int
tic6x_unrecognized_line (int c)
{
  if (c == '|')
    return handle_parallel_marker();
  if (c == '[')
    return handle_predicate();
  return 0;
}

static int
handle_parallel_marker (void)
{
  if (input_line_pointer[0] != '|')
    return 0;
    
  if (input_line_pointer[1] == '^')
    {
      tic6x_line_spmask = true;
      input_line_pointer += 2;
    }
  else
    input_line_pointer += 1;
    
  if (tic6x_line_parallel)
    as_bad (_("multiple '||' on same line"));
  tic6x_line_parallel = true;
  
  if (tic6x_line_creg)
    as_bad (_("'||' after predicate"));
    
  return 1;
}

static int
handle_predicate (void)
{
  char *endp = find_predicate_end();
  if (endp == NULL)
    return 0;
    
  predicate_info_t pred_info = parse_predicate();
  
  if (tic6x_line_creg)
    as_bad (_("multiple predicates on same line"));
    
  if (pred_info.bad_predicate)
    {
      report_bad_predicate(endp);
      return 1;
    }
    
  set_predicate_register(pred_info);
  tic6x_line_z = pred_info.z;
  
  return 1;
}

static char *
find_predicate_end (void)
{
  char *p = input_line_pointer;
  while (*p != ']' && !is_end_of_stmt (*p))
    p++;
  return (*p == ']') ? p + 1 : NULL;
}

static predicate_info_t
parse_predicate (void)
{
  predicate_info_t info = {0, true, false};
  char *p = input_line_pointer;
  
  if (*p == '!')
    {
      info.z = 1;
      p++;
    }
    
  if (!parse_register_type(p, &info.areg))
    {
      info.bad_predicate = true;
      return info;
    }
    
  p++;
  if (!is_valid_register_number(*p) || p[1] != ']')
    {
      info.bad_predicate = true;
      return info;
    }
    
  info.register_num = *p;
  info.bad_predicate = false;
  input_line_pointer = p + 2;
  
  return info;
}

static bool
parse_register_type (char *p, bool *areg)
{
  if (*p == 'A' || *p == 'a')
    {
      *areg = true;
      return true;
    }
  if (*p == 'B' || *p == 'b')
    {
      *areg = false;
      return true;
    }
  *areg = true;
  return false;
}

static bool
is_valid_register_number (char c)
{
  return (c == '0' || c == '1' || c == '2');
}

static void
report_bad_predicate (char *endp)
{
  char ctmp = *endp;
  *endp = 0;
  as_bad (_("bad predicate '%s'"), input_line_pointer - 1);
  *endp = ctmp;
  input_line_pointer = endp;
}

static void
set_predicate_register (predicate_info_t info)
{
  #define AREG_0 6
  #define AREG_1 4
  #define AREG_2 5
  #define BREG_0 1
  #define BREG_1 2
  #define BREG_2 3
  
  switch (info.register_num)
    {
    case '0':
      tic6x_line_creg = info.areg ? AREG_0 : BREG_0;
      if (info.areg && !tic6x_predicate_a0)
        as_bad (_("predication on A0 not supported on this architecture"));
      break;
    case '1':
      tic6x_line_creg = info.areg ? AREG_1 : BREG_1;
      break;
    case '2':
      tic6x_line_creg = info.areg ? AREG_2 : BREG_2;
      break;
    default:
      abort ();
    }
}

typedef struct {
  unsigned int z;
  bool areg;
  bool bad_predicate;
  char register_num;
} predicate_info_t;

/* Do any target-specific handling of a label required.  */

void
tic6x_frob_label (symbolS *sym)
{
  check_parallel_label_error();
  check_predicate_label_error();
  add_label_to_segment(sym);
  dwarf2_emit_label (sym);
}

static void
check_parallel_label_error(void)
{
  if (tic6x_line_parallel)
    {
      as_bad (_("label after '||'"));
      tic6x_line_parallel = false;
      tic6x_line_spmask = false;
    }
}

static void
check_predicate_label_error(void)
{
  if (tic6x_line_creg)
    {
      as_bad (_("label after predicate"));
      tic6x_line_creg = 0;
      tic6x_line_z = 0;
    }
}

static void
add_label_to_segment(symbolS *sym)
{
  segment_info_type *si = seg_info (now_seg);
  tic6x_label_list *list = si->tc_segment_info_data.label_list;
  si->tc_segment_info_data.label_list = XNEW (tic6x_label_list);
  si->tc_segment_info_data.label_list->next = list;
  si->tc_segment_info_data.label_list->label = sym;
}

/* At end-of-line, give errors for start-of-line decorations that
   needed an instruction but were not followed by one.  */

static void
tic6x_end_of_line (void)
{
  if (tic6x_line_parallel)
    {
      as_bad (_("'||' not followed by instruction"));
      tic6x_line_parallel = false;
      tic6x_line_spmask = false;
    }
  if (tic6x_line_creg)
    {
      as_bad (_("predicate not followed by instruction"));
      tic6x_line_creg = 0;
      tic6x_line_z = 0;
    }
}

/* Do any target-specific handling of the start of a logical line.  */

void tic6x_start_line_hook(void)
{
    tic6x_end_of_line();
}

/* Do target-specific handling immediately after an input file from
   the command line, and any other inputs it includes, have been
   read.  */

void tic6x_cleanup(void)
{
    tic6x_end_of_line();
}

/* Do target-specific initialization after arguments have been
   processed and the output file created.  */

void
tic6x_init_after_args (void)
{
  elf32_tic6x_set_use_rela_p (stdoutput, tic6x_generate_rela);
}

/* Free LIST of labels (possibly NULL).  */

static void
tic6x_free_label_list (tic6x_label_list *list)
{
  while (list)
    {
      tic6x_label_list *old = list;
      list = list->next;
      free (old);
    }
}

/* Handle a data alignment of N bytes.  */

void
tic6x_cons_align (int n ATTRIBUTE_UNUSED)
{
  segment_info_type *seginfo = seg_info (now_seg);
  
  tic6x_free_label_list (seginfo->tc_segment_info_data.label_list);
  seginfo->tc_segment_info_data.label_list = NULL;
  seginfo->tc_segment_info_data.execute_packet_frag = NULL;
  seginfo->tc_segment_info_data.last_insn_lsb = NULL;
  seginfo->tc_segment_info_data.spmask_addr = NULL;
  seginfo->tc_segment_info_data.func_units_used = 0;
}

/* Handle an alignment directive.  Return TRUE if the
   machine-independent frag generation should be skipped.  */

bool
tic6x_do_align (int n, char *fill, int len ATTRIBUTE_UNUSED, int max)
{
  if (!is_valid_alignment_request(n, max, fill))
    return false;

  if (n > 5)
    return false;

  prepare_fragment_for_alignment();
  create_alignment_fragment(n, max);
  
  return true;
}

static bool
is_valid_alignment_request(int n, char *fill, int max)
{
  return n > 0
      && max >= 0
      && max < (1 << n)
      && !need_pass_2
      && fill == NULL
      && subseg_text_p (now_seg);
}

static void
prepare_fragment_for_alignment(void)
{
  if (frag_now_fix () != 0)
    {
      if (frag_now->fr_type != rs_machine_dependent)
        frag_wane (frag_now);

      frag_new (0);
    }
}

static void
create_alignment_fragment(int n, int max)
{
  fragS *align_frag;
  char *p;

  frag_grow (32);
  align_frag = frag_now;
  p = frag_var (rs_machine_dependent, 32, 32, max, NULL, n, NULL);
  
  if (p != align_frag->fr_literal)
    abort ();
    
  align_frag->tc_frag_data.is_insns = false;
}

/* Types of operand for parsing purposes.  These are used as bit-masks
   to tell tic6x_parse_operand what forms of operand are
   permitted.  */
#define TIC6X_OP_EXP		0x0001u
#define TIC6X_OP_REG		0x0002u
#define TIC6X_OP_REGPAIR	0x0004u
#define TIC6X_OP_IRP		0x0008u
#define TIC6X_OP_NRP		0x0010u
/* With TIC6X_OP_MEM_NOUNREG, the contents of a () offset are always
   interpreted as an expression, which may be a symbol with the same
   name as a register that ends up being implicitly DP-relative.  With
   TIC6X_OP_MEM_UNREG, the contents of a () offset are interpreted as
   a register if they match one, and failing that as an expression,
   which must be constant.  */
#define TIC6X_OP_MEM_NOUNREG	0x0020u
#define TIC6X_OP_MEM_UNREG	0x0040u
#define TIC6X_OP_CTRL		0x0080u
#define TIC6X_OP_FUNC_UNIT	0x0100u

/* A register or register pair read by the assembler.  */
typedef struct
{
  /* The side the register is on (1 or 2).  */
  unsigned int side;
  /* The register number (0 to 31).  */
  unsigned int num;
} tic6x_register;

/* Types of modification of a base address.  */
typedef enum
  {
    tic6x_mem_mod_none,
    tic6x_mem_mod_plus,
    tic6x_mem_mod_minus,
    tic6x_mem_mod_preinc,
    tic6x_mem_mod_predec,
    tic6x_mem_mod_postinc,
    tic6x_mem_mod_postdec
  } tic6x_mem_mod;

/* Scaled [] or unscaled () nature of an offset.  */
typedef enum
  {
    tic6x_offset_none,
    tic6x_offset_scaled,
    tic6x_offset_unscaled
  } tic6x_mem_scaling;

/* A memory operand read by the assembler.  */
typedef struct
{
  /* The base register.  */
  tic6x_register base_reg;
  /* How the base register is modified.  */
  tic6x_mem_mod mod;
  /* Whether there is an offset (required with plain "+" and "-"), and
     whether it is scaled or unscaled if so.  */
  tic6x_mem_scaling scaled;
  /* Whether the offset is a register (TRUE) or an expression
     (FALSE).  */
  bool offset_is_reg;
  /* The offset.  */
  union
  {
    expressionS exp;
    tic6x_register reg;
  } offset;
} tic6x_mem_ref;

/* A functional unit in SPMASK operands read by the assembler.  */
typedef struct
{
  /* The basic unit.  */
  tic6x_func_unit_base base;
  /* The side (1 or 2).  */
  unsigned int side;
} tic6x_func_unit_operand;

/* An operand read by the assembler.  */
typedef struct
{
  /* The syntactic form of the operand, as one of the bit-masks
     above.  */
  unsigned int form;
  /* The operand value.  */
  union
  {
    /* An expression: TIC6X_OP_EXP.  */
    expressionS exp;
    /* A register: TIC6X_OP_REG, TIC6X_OP_REGPAIR.  */
    tic6x_register reg;
    /* A memory reference: TIC6X_OP_MEM_NOUNREG,
       TIC6X_OP_MEM_UNREG.  */
    tic6x_mem_ref mem;
    /* A control register: TIC6X_OP_CTRL.  */
    tic6x_ctrl_id ctrl;
    /* A functional unit: TIC6X_OP_FUNC_UNIT.  */
    tic6x_func_unit_operand func_unit;
  } value;
} tic6x_operand;

#define skip_whitespace(str)  do { if (is_whitespace (*(str))) ++(str); } while (0)

/* Parse a register operand, or part of an operand, starting at *P.
   If syntactically OK (including that the number is in the range 0 to
   31, but not necessarily in range for this architecture), return
   TRUE, putting the register side and number in *REG and update *P to
   point immediately after the register number; otherwise return FALSE
   without changing *P (but possibly changing *REG).  Do not print any
   diagnostics.  */

static bool is_digit(char c)
{
    return c >= '0' && c <= '9';
}

static bool parse_register_side(char c, int *side)
{
    switch (c)
    {
    case 'a':
    case 'A':
        *side = 1;
        return true;
    case 'b':
    case 'B':
        *side = 2;
        return true;
    default:
        return false;
    }
}

static bool parse_first_digit(char **r, int *num)
{
    if (!is_digit(**r))
        return false;
    
    *num = **r - '0';
    (*r)++;
    return true;
}

static void parse_second_digit(char **r, int *num)
{
    if (*num > 0 && is_digit(**r))
    {
        *num = *num * 10 + (**r - '0');
        (*r)++;
    }
}

static bool validate_register_number(char *r, int num)
{
    return !is_digit(*r) && num < 32;
}

static bool tic6x_parse_register(char **p, tic6x_register *reg)
{
    char *r = *p;

    if (!parse_register_side(*r, &reg->side))
        return false;
    r++;

    if (!parse_first_digit(&r, &reg->num))
        return false;

    parse_second_digit(&r, &reg->num);

    if (!validate_register_number(r, reg->num))
        return false;

    *p = r;
    return true;
}

/* Parse the initial two characters of a functional unit name starting
   at *P.  If OK, set *BASE and *SIDE and return true; otherwise,
   return FALSE.  */

static tic6x_func_unit_base get_func_unit_base(char unit_char)
{
    switch (unit_char)
    {
    case 'd':
    case 'D':
        return tic6x_func_unit_d;
    case 'l':
    case 'L':
        return tic6x_func_unit_l;
    case 'm':
    case 'M':
        return tic6x_func_unit_m;
    case 's':
    case 'S':
        return tic6x_func_unit_s;
    default:
        return tic6x_func_unit_nfu;
    }
}

static unsigned int get_side_number(char side_char)
{
    switch (side_char)
    {
    case '1':
        return 1;
    case '2':
        return 2;
    default:
        return 0;
    }
}

static bool
tic6x_parse_func_unit_base (char *p, tic6x_func_unit_base *base,
			    unsigned int *side)
{
    tic6x_func_unit_base maybe_base = get_func_unit_base(p[0]);
    if (maybe_base == tic6x_func_unit_nfu)
        return false;

    unsigned int maybe_side = get_side_number(p[1]);
    if (maybe_side == 0)
        return false;

    *base = maybe_base;
    *side = maybe_side;
    return true;
}

/* Parse an operand starting at *P.  If the operand parses OK, return
   TRUE and store the value in *OP; otherwise return FALSE (possibly
   changing *OP).  In any case, update *P to point to the following
   comma or end of line.  The possible operand forms are given by
   OP_FORMS.  For diagnostics, this is operand OPNO of an opcode
   starting at STR, length OPC_LEN.  */

static bool
parse_func_unit(char **q, tic6x_operand *op, unsigned int op_forms)
{
    tic6x_func_unit_base base = tic6x_func_unit_nfu;
    unsigned int side = 0;

    if (!(op_forms & TIC6X_OP_FUNC_UNIT))
        return false;

    if (!tic6x_parse_func_unit_base(*q, &base, &side))
        return false;

    char *rq = *q + 2;
    skip_whitespace(rq);
    if (!is_end_of_stmt(*rq) && *rq != ',')
        return false;

    op->form = TIC6X_OP_FUNC_UNIT;
    op->value.func_unit.base = base;
    op->value.func_unit.side = side;
    *q = rq;
    return true;
}

static bool
parse_literal_string(char **q, const char *literal, tic6x_op_form form_type, tic6x_operand *op, unsigned int op_forms)
{
    if (!(op_forms & form_type))
        return false;

    size_t len = strlen(literal);
    if (strncasecmp(*q, literal, len) != 0)
        return false;

    char *rq = *q + len;
    skip_whitespace(rq);
    if (!is_end_of_stmt(*rq) && *rq != ',')
        return false;

    op->form = form_type;
    *q = rq;
    return true;
}

static bool
parse_control_register(char **q, tic6x_operand *op, unsigned int op_forms)
{
    if (!(op_forms & TIC6X_OP_CTRL))
        return false;

    for (tic6x_ctrl_id crid = 0; crid < tic6x_ctrl_max; crid++) {
        size_t len = strlen(tic6x_ctrl_table[crid].name);
        if (strncasecmp(tic6x_ctrl_table[crid].name, *q, len) != 0)
            continue;

        char *rq = *q + len;
        skip_whitespace(rq);
        if (!is_end_of_stmt(*rq) && *rq != ',')
            continue;

        op->form = TIC6X_OP_CTRL;
        op->value.ctrl = crid;
        *q = rq;
        
        if (!(tic6x_ctrl_table[crid].isa_variants & tic6x_features))
            as_bad(_("control register '%s' not supported on this architecture"),
                   tic6x_ctrl_table[crid].name);
        return true;
    }
    return false;
}

static tic6x_mem_mod
parse_mem_modifier(char **mq)
{
    switch (**mq) {
    case '+':
        if ((*mq)[1] == '+') {
            *mq += 2;
            return tic6x_mem_mod_preinc;
        }
        (*mq)++;
        return tic6x_mem_mod_plus;
    case '-':
        if ((*mq)[1] == '-') {
            *mq += 2;
            return tic6x_mem_mod_predec;
        }
        (*mq)++;
        return tic6x_mem_mod_minus;
    default:
        return tic6x_mem_mod_none;
    }
}

static bool
parse_post_modifier(char **mq, tic6x_mem_mod *mem_mod)
{
    skip_whitespace(*mq);
    if ((*mq)[0] == '+' && (*mq)[1] == '+') {
        *mem_mod = tic6x_mem_mod_postinc;
        *mq += 2;
        return true;
    }
    if ((*mq)[0] == '-' && (*mq)[1] == '-') {
        *mem_mod = tic6x_mem_mod_postdec;
        *mq += 2;
        return true;
    }
    return false;
}

static bool
parse_offset(char **mq, tic6x_mem_scaling *scaled, bool *offset_is_reg,
            tic6x_register *offset_reg, expressionS *offset_exp, unsigned int op_forms)
{
    char endc = 0;
    skip_whitespace(*mq);
    
    switch (**mq) {
    case '[':
        *scaled = tic6x_offset_scaled;
        endc = ']';
        (*mq)++;
        break;
    case '(':
        *scaled = tic6x_offset_unscaled;
        endc = ')';
        (*mq)++;
        break;
    default:
        return true;
    }

    skip_whitespace(*mq);
    if (*scaled == tic6x_offset_scaled || (op_forms & TIC6X_OP_MEM_UNREG)) {
        char *rq = *mq;
        if (tic6x_parse_register(&rq, offset_reg)) {
            skip_whitespace(rq);
            if (*rq == endc) {
                *mq = rq;
                *offset_is_reg = true;
            }
        }
    }

    if (!*offset_is_reg) {
        char *save_input_line_pointer = input_line_pointer;
        input_line_pointer = *mq;
        expression(offset_exp);
        *mq = input_line_pointer;
        input_line_pointer = save_input_line_pointer;
    }

    skip_whitespace(*mq);
    if (**mq != endc)
        return false;
    (*mq)++;
    return true;
}

static void
validate_register_support(tic6x_register reg)
{
    if (reg.num >= tic6x_num_registers)
        as_bad(_("register number %u not supported on this architecture"), reg.num);
}

static bool
parse_memory_reference(char **q, tic6x_operand *op, unsigned int op_forms)
{
    if (!(op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG)))
        return false;

    char *mq = *q;
    if (*mq != '*')
        return false;
    mq++;

    skip_whitespace(mq);
    tic6x_mem_mod mem_mod = parse_mem_modifier(&mq);

    tic6x_register base_reg;
    skip_whitespace(mq);
    if (!tic6x_parse_register(&mq, &base_reg))
        return false;

    if (mem_mod == tic6x_mem_mod_none)
        parse_post_modifier(&mq, &mem_mod);

    bool permit_offset = (mem_mod != tic6x_mem_mod_none);
    bool require_offset = (mem_mod == tic6x_mem_mod_plus || mem_mod == tic6x_mem_mod_minus);
    
    tic6x_mem_scaling scaled = tic6x_offset_none;
    bool offset_is_reg = false;
    tic6x_register offset_reg;
    expressionS offset_exp;

    if (permit_offset && !parse_offset(&mq, &scaled, &offset_is_reg, &offset_reg, &offset_exp, op_forms))
        return false;

    if (require_offset && scaled == tic6x_offset_none)
        return false;

    skip_whitespace(mq);
    if (!is_end_of_stmt(*mq) && *mq != ',')
        return false;

    op->form = op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG);
    op->value.mem.base_reg = base_reg;
    op->value.mem.mod = mem_mod;
    op->value.mem.scaled = scaled;
    op->value.mem.offset_is_reg = offset_is_reg;
    if (offset_is_reg)
        op->value.mem.offset.reg = offset_reg;
    else
        op->value.mem.offset.exp = offset_exp;

    *q = mq;
    validate_register_support(base_reg);
    if (offset_is_reg)
        validate_register_support(offset_reg);
    return true;
}

static bool
parse_register_pair(char **rq, tic6x_register *first_reg, tic6x_register *second_reg, 
                   unsigned int opno, char *str, int opc_len)
{
    (*rq)++;
    if (!tic6x_parse_register(rq, second_reg))
        return false;

    skip_whitespace(*rq);
    if (!is_end_of_stmt(**rq) && **rq != ',')
        return false;

    if ((second_reg->num & 1) || (first_reg->num != second_reg->num + 1) ||
        (first_reg->side != second_reg->side)) {
        as_bad(_("register pair for operand %u of '%.*s' not a valid even/odd pair"),
               opno, opc_len, str);
    }
    return true;
}

static bool
parse_register_or_pair(char **q, tic6x_operand *op, unsigned int op_forms,
                      unsigned int opno, char *str, int opc_len)
{
    if (!(op_forms & (TIC6X_OP_REG | TIC6X_OP_REGPAIR)))
        return false;

    char *rq = *q;
    tic6x_register first_reg, second_reg;
    
    if (!tic6x_parse_register(&rq, &first_reg))
        return false;

    if (*rq == ':' && (op_forms & TIC6X_OP_REGPAIR)) {
        if (!parse_register_pair(&rq, &first_reg, &second_reg, opno, str, opc_len))
            return false;
        op->form = TIC6X_OP_REGPAIR;
        op->value.reg = second_reg;
    } else if (op_forms & TIC6X_OP_REG) {
        skip_whitespace(rq);
        if (!is_end_of_stmt(*rq) && *rq != ',')
            return false;
        op->form = TIC6X_OP_REG;
        op->value.reg = first_reg;
    } else {
        return false;
    }

    *q = rq;
    validate_register_support(first_reg);
    if (op->form == TIC6X_OP_REGPAIR)
        validate_register_support(second_reg);
    return true;
}

static bool
parse_expression(char **q, tic6x_operand *op, unsigned int op_forms)
{
    if (!(op_forms & TIC6X_OP_EXP))
        return false;

    char *save_input_line_pointer = input_line_pointer;
    input_line_pointer = *q;
    op->form = TIC6X_OP_EXP;
    expression(&op->value.exp);
    *q = input_line_pointer;
    input_line_pointer = save_input_line_pointer;
    return true;
}

static void
skip_to_next_operand(char **q)
{
    while (!is_end_of_stmt(**q) && **q != ',')
        (*q)++;
}

static void
report_parse_error(unsigned int op_forms, unsigned int opno, char *str, int opc_len)
{
    switch (op_forms) {
    case TIC6X_OP_REG | TIC6X_OP_REGPAIR:
        as_bad(_("bad register or register pair for operand %u of '%.*s'"),
               opno, opc_len, str);
        break;
    case TIC6X_OP_REG | TIC6X_OP_CTRL:
    case TIC6X_OP_REG:
        as_bad(_("bad register for operand %u of '%.*s'"), opno, opc_len, str);
        break;
    case TIC6X_OP_REGPAIR:
        as_bad(_("bad register pair for operand %u of '%.*s'"), opno, opc_len, str);
        break;
    case TIC6X_OP_FUNC_UNIT:
        as_bad(_("bad functional unit for operand %u of '%.*s'"), opno, opc_len, str);
        break;
    default:
        as_bad(_("bad operand %u of '%.*s'"), opno, opc_len, str);
        break;
    }
}

static bool
tic6x_parse_operand(char **p, tic6x_operand *op, unsigned int op_forms,
                   char *str, int opc_len, unsigned int opno)
{
    if ((op_forms & (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG)) ==
        (TIC6X_OP_MEM_NOUNREG | TIC6X_OP_MEM_UNREG))
        abort();

    char *q = *p;
    bool operand_parsed = false;

    if (!operand_parsed)
        operand_parsed = parse_func_unit(&q, op, op_forms);
    
    if (!operand_parsed)
        operand_parsed = parse_literal_string(&q, "irp", TIC6X_OP_IRP, op, op_forms);
    
    if (!operand_parsed)
        operand_parsed = parse_literal_string(&q, "nrp", TIC6X_OP_NRP, op, op_forms);
    
    if (!operand_parsed)
        operand_parsed = parse_control_register(&q, op, op_forms);
    
    if (!operand_parsed)
        operand_parsed = parse_memory_reference(&q, op, op_forms);
    
    if (!operand_parsed)
        operand_parsed = parse_register_or_pair(&q, op, op_forms, opno, str, opc_len);
    
    if (!operand_parsed)
        operand_parsed = parse_expression(&q, op, op_forms);

    if (operand_parsed) {
        skip_whitespace(q);
        if (!is_end_of_stmt(*q) && *q != ',') {
            operand_parsed = false;
            as_bad(_("junk after operand %u of '%.*s'"), opno, opc_len, str);
            skip_to_next_operand(&q);
        }
    } else {
        report_parse_error(op_forms, opno, str, opc_len);
        skip_to_next_operand(&q);
    }

    *p = q;
    return operand_parsed;
}

/* Table of assembler operators and associated O_* values.  */
typedef struct
{
  const char *name;
  operatorT op;
} tic6x_operator_table;
static const tic6x_operator_table tic6x_operators[] = {
#define O_dsbt_index O_md1
  { "dsbt_index", O_dsbt_index },
#define O_got O_md2
  { "got", O_got },
#define O_dpr_got O_md3
  { "dpr_got", O_dpr_got },
#define O_dpr_byte O_md4
  { "dpr_byte", O_dpr_byte },
#define O_dpr_hword O_md5
  { "dpr_hword", O_dpr_hword },
#define O_dpr_word O_md6
  { "dpr_word", O_dpr_word },
#define O_pcr_offset O_md7
  { "pcr_offset", O_pcr_offset }
};

/* Parse a name in some machine-specific way.  Used on C6X to handle
   assembler operators.  */

int
tic6x_parse_name (const char *name, expressionS *exprP,
		  enum expr_mode mode ATTRIBUTE_UNUSED, char *nextchar)
{
  char *p = input_line_pointer;
  char c, *name_start, *name_end;
  const char *inner_name;
  unsigned int i;
  operatorT op = O_illegal;
  symbolS *sym, *op_sym = NULL;

  if (*name != '$')
    return 0;

  op = find_operator(name + 1);
  if (op == O_illegal)
    return 0;

  *input_line_pointer = *nextchar;
  skip_whitespace (p);

  if (!expect_and_advance_char(&p, '('))
    return 0;

  skip_whitespace (p);

  if (!parse_name(&p, &name_start, &name_end))
    return 0;

  skip_whitespace (p);

  if (op == O_pcr_offset)
    {
      if (!parse_pcr_offset_operator(&p, &op_sym))
        return 0;
      skip_whitespace (p);
    }

  if (!expect_char(p, ')'))
    return 0;

  input_line_pointer = p + 1;
  *nextchar = *input_line_pointer;
  *input_line_pointer = 0;

  inner_name = get_validated_inner_name(op, name_start, name_end);
  sym = symbol_find_or_make (inner_name);

  set_expression(exprP, op, sym, op_sym);

  return 1;
}

static operatorT find_operator(const char *op_name)
{
  unsigned int i;
  for (i = 0; i < ARRAY_SIZE (tic6x_operators); i++)
    if (strcasecmp (op_name, tic6x_operators[i].name) == 0)
      return tic6x_operators[i].op;
  return O_illegal;
}

static int expect_and_advance_char(char **p, char expected)
{
  if (**p != expected)
    {
      *input_line_pointer = 0;
      return 0;
    }
  (*p)++;
  return 1;
}

static int expect_char(char *p, char expected)
{
  if (*p != expected)
    {
      *input_line_pointer = 0;
      return 0;
    }
  return 1;
}

static int parse_name(char **p, char **name_start, char **name_end)
{
  if (!is_name_beginner (**p))
    {
      *input_line_pointer = 0;
      return 0;
    }

  *name_start = *p;
  (*p)++;
  while (is_part_of_name (**p))
    (*p)++;
  *name_end = *p;
  return 1;
}

static int parse_pcr_offset_operator(char **p, symbolS **op_sym)
{
  char *op_name_start, *op_name_end;
  char c;

  if (!expect_and_advance_char(p, ','))
    return 0;
    
  skip_whitespace (*p);

  if (!parse_name(p, &op_name_start, &op_name_end))
    return 0;

  c = *op_name_end;
  *op_name_end = 0;
  *op_sym = symbol_find_or_make (op_name_start);
  *op_name_end = c;
  
  return 1;
}

static const char* get_validated_inner_name(operatorT op, char *name_start, char *name_end)
{
  char c;
  const char *inner_name;
  
  c = *name_end;
  *name_end = 0;
  inner_name = name_start;
  
  if (op == O_dsbt_index && strcmp (inner_name, "__c6xabi_DSBT_BASE") != 0)
    {
      as_bad (_("$DSBT_INDEX must be used with __c6xabi_DSBT_BASE"));
      inner_name = "__c6xabi_DSBT_BASE";
    }
  
  *name_end = c;
  return inner_name;
}

static void set_expression(expressionS *exprP, operatorT op, symbolS *sym, symbolS *op_sym)
{
  exprP->X_op = op;
  exprP->X_add_symbol = sym;
  exprP->X_add_number = 0;
  exprP->X_op_symbol = op_sym;
  exprP->X_md = 0;
}

/* Create a fixup for an expression.  Same arguments as fix_new_exp,
   plus FIX_ADDA which is TRUE for ADDA instructions (to indicate that
   fixes resolving to constants should have those constants implicitly
   shifted) and FALSE otherwise, but look for C6X-specific expression
   types and adjust the relocations or give errors accordingly.  */

static bfd_reloc_code_real_type
get_dsbt_index_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_SBR_U15_W)
        return BFD_RELOC_C6000_DSBT_INDEX;
    
    as_bad(_("$DSBT_INDEX not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_got_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_SBR_U15_W)
        return BFD_RELOC_C6000_SBR_GOT_U15_W;
    
    as_bad(_("$GOT not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_dpr_got_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_ABS_L16)
        return BFD_RELOC_C6000_SBR_GOT_L16_W;
    if (r_type == BFD_RELOC_C6000_ABS_H16)
        return BFD_RELOC_C6000_SBR_GOT_H16_W;
    
    as_bad(_("$DPR_GOT not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_dpr_byte_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_ABS_S16)
        return BFD_RELOC_C6000_SBR_S16;
    if (r_type == BFD_RELOC_C6000_ABS_L16)
        return BFD_RELOC_C6000_SBR_L16_B;
    if (r_type == BFD_RELOC_C6000_ABS_H16)
        return BFD_RELOC_C6000_SBR_H16_B;
    
    as_bad(_("$DPR_BYTE not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_dpr_hword_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_ABS_L16)
        return BFD_RELOC_C6000_SBR_L16_H;
    if (r_type == BFD_RELOC_C6000_ABS_H16)
        return BFD_RELOC_C6000_SBR_H16_H;
    
    as_bad(_("$DPR_HWORD not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_dpr_word_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_ABS_L16)
        return BFD_RELOC_C6000_SBR_L16_W;
    if (r_type == BFD_RELOC_C6000_ABS_H16)
        return BFD_RELOC_C6000_SBR_H16_W;
    
    as_bad(_("$DPR_WORD not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_pcr_offset_reloc(bfd_reloc_code_real_type r_type)
{
    if (r_type == BFD_RELOC_C6000_ABS_S16 || r_type == BFD_RELOC_C6000_ABS_L16)
        return BFD_RELOC_C6000_PCR_L16;
    if (r_type == BFD_RELOC_C6000_ABS_H16)
        return BFD_RELOC_C6000_PCR_H16;
    
    as_bad(_("$PCR_OFFSET not supported in this context"));
    return BFD_RELOC_UNUSED;
}

static bfd_reloc_code_real_type
get_new_reloc(expressionS *exp, bfd_reloc_code_real_type r_type, symbolS **subsy)
{
    switch (exp->X_op)
    {
    case O_dsbt_index:
        return get_dsbt_index_reloc(r_type);
    case O_got:
        return get_got_reloc(r_type);
    case O_dpr_got:
        return get_dpr_got_reloc(r_type);
    case O_dpr_byte:
        return get_dpr_byte_reloc(r_type);
    case O_dpr_hword:
        return get_dpr_hword_reloc(r_type);
    case O_dpr_word:
        return get_dpr_word_reloc(r_type);
    case O_pcr_offset:
        *subsy = exp->X_op_symbol;
        return get_pcr_offset_reloc(r_type);
    default:
        return BFD_RELOC_UNUSED;
    }
}

static fixS *
create_fix(fragS *frag, int where, int size, expressionS *exp,
           int pcrel, bfd_reloc_code_real_type new_reloc, bfd_reloc_code_real_type r_type)
{
    if (new_reloc == BFD_RELOC_UNUSED)
        return fix_new_exp(frag, where, size, exp, pcrel, r_type);
    
    return fix_new(frag, where, size, exp->X_add_symbol, exp->X_add_number,
                   pcrel, new_reloc);
}

static void
tic6x_fix_new_exp(fragS *frag, int where, int size, expressionS *exp,
                  int pcrel, bfd_reloc_code_real_type r_type,
                  bool fix_adda)
{
    symbolS *subsy = NULL;
    fixS *fix;
    
    bfd_reloc_code_real_type new_reloc = get_new_reloc(exp, r_type, &subsy);
    
    if (new_reloc == BFD_RELOC_UNUSED && exp->X_op != O_symbol && pcrel)
    {
        as_bad(_("invalid PC-relative operand"));
        return;
    }
    
    fix = create_fix(frag, where, size, exp, pcrel, new_reloc, r_type);
    fix->tc_fix_data.fix_subsy = subsy;
    fix->tc_fix_data.fix_adda = fix_adda;
}

/* Generate a fix for a constant (.word etc.).  Needed to ensure these
   go through the error checking in tic6x_fix_new_exp.  */

void
tic6x_cons_fix_new (fragS *frag, int where, int size, expressionS *exp,
		    bfd_reloc_code_real_type r_type)
{
  static const int BYTE_SIZE = 1;
  static const int WORD_SIZE = 2;
  static const int DWORD_SIZE = 4;
  
  switch (size)
    {
    case BYTE_SIZE:
      r_type = BFD_RELOC_8;
      break;

    case WORD_SIZE:
      r_type = BFD_RELOC_16;
      break;

    case DWORD_SIZE:
      r_type = BFD_RELOC_32;
      break;

    default:
      as_bad (_("no %d-byte relocations available"), size);
      return;
    }

  tic6x_fix_new_exp (frag, where, size, exp, 0, r_type, false);
}

/* Initialize target-specific fix data.  */

void
tic6x_init_fix_data (fixS *fixP)
{
  fixP->tc_fix_data.fix_adda = false;
  fixP->tc_fix_data.fix_subsy = NULL;
}

/* Return true if the fix can be handled by GAS, false if it must
   be passed through to the linker.  */

bool
tic6x_fix_adjustable (fixS *fixP)
{
  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
    case BFD_RELOC_C6000_EHTYPE:
    case BFD_RELOC_C6000_PREL31:
    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      return 0;

    default:
      return 1;
    }
}

/* Given the fine-grained form of an operand, return the coarse
   (bit-mask) form.  */

static unsigned int
tic6x_coarse_operand_form (tic6x_operand_form form)
{
  static const struct {
    tic6x_operand_form form;
    unsigned int result;
  } form_map[] = {
    { tic6x_operand_asm_const, TIC6X_OP_EXP },
    { tic6x_operand_link_const, TIC6X_OP_EXP },
    { tic6x_operand_reg, TIC6X_OP_REG },
    { tic6x_operand_xreg, TIC6X_OP_REG },
    { tic6x_operand_dreg, TIC6X_OP_REG },
    { tic6x_operand_areg, TIC6X_OP_REG },
    { tic6x_operand_retreg, TIC6X_OP_REG },
    { tic6x_operand_regpair, TIC6X_OP_REGPAIR },
    { tic6x_operand_xregpair, TIC6X_OP_REGPAIR },
    { tic6x_operand_dregpair, TIC6X_OP_REGPAIR },
    { tic6x_operand_irp, TIC6X_OP_IRP },
    { tic6x_operand_nrp, TIC6X_OP_NRP },
    { tic6x_operand_ctrl, TIC6X_OP_CTRL },
    { tic6x_operand_mem_short, TIC6X_OP_MEM_NOUNREG },
    { tic6x_operand_mem_long, TIC6X_OP_MEM_NOUNREG },
    { tic6x_operand_mem_deref, TIC6X_OP_MEM_NOUNREG },
    { tic6x_operand_mem_ndw, TIC6X_OP_MEM_UNREG },
    { tic6x_operand_func_unit, TIC6X_OP_FUNC_UNIT }
  };
  
  const size_t map_size = sizeof(form_map) / sizeof(form_map[0]);
  
  for (size_t i = 0; i < map_size; i++)
    {
      if (form_map[i].form == form)
        return form_map[i].result;
    }
  
  abort ();
}

/* How an operand may match or not match a desired form.  If different
   instruction alternatives fail in different ways, the first failure
   in this list determines the diagnostic.  */
typedef enum
  {
    /* Matches.  */
    tic6x_match_matches,
    /* Bad coarse form.  */
    tic6x_match_coarse,
    /* Not constant.  */
    tic6x_match_non_const,
    /* Register on wrong side.  */
    tic6x_match_wrong_side,
    /* Not a valid address register.  */
    tic6x_match_bad_address,
    /* Not a valid return address register.  */
    tic6x_match_bad_return,
    /* Control register not readable.  */
    tic6x_match_ctrl_write_only,
    /* Control register not writable.  */
    tic6x_match_ctrl_read_only,
    /* Not a valid memory reference for this instruction.  */
    tic6x_match_bad_mem
  } tic6x_operand_match;

/* Return whether an operand matches the given fine-grained form and
   read/write usage, and, if it does not match, how it fails to match.
   The main functional unit side is SIDE; the cross-path side is CROSS
   (the same as SIDE if a cross path not used); the data side is
   DATA_SIDE.  */
#define AREG_B14 14
#define AREG_B15 15
#define RETREG_NUM 3

static tic6x_operand_match
check_side_match(unsigned int reg_side, unsigned int expected_side)
{
    return (reg_side == expected_side) ? tic6x_match_matches : tic6x_match_wrong_side;
}

static tic6x_operand_match
check_areg_validity(const tic6x_operand *op, unsigned int cross)
{
    if (op->value.reg.side != cross)
        return tic6x_match_wrong_side;
    if (op->value.reg.side == 2 && 
        (op->value.reg.num == AREG_B14 || op->value.reg.num == AREG_B15))
        return tic6x_match_matches;
    return tic6x_match_bad_address;
}

static tic6x_operand_match
check_retreg_validity(const tic6x_operand *op, unsigned int side)
{
    if (op->value.reg.side != side)
        return tic6x_match_wrong_side;
    if (op->value.reg.num != RETREG_NUM)
        return tic6x_match_bad_return;
    return tic6x_match_matches;
}

static tic6x_operand_match
check_ctrl_access(const tic6x_operand *op, tic6x_rw rw)
{
    tic6x_rw ctrl_rw = tic6x_ctrl_table[op->value.ctrl].rw;
    
    if (rw == tic6x_rw_read)
    {
        if (ctrl_rw == tic6x_rw_read || ctrl_rw == tic6x_rw_read_write)
            return tic6x_match_matches;
        return tic6x_match_ctrl_write_only;
    }
    if (rw == tic6x_rw_write)
    {
        if (ctrl_rw == tic6x_rw_write || ctrl_rw == tic6x_rw_read_write)
            return tic6x_match_matches;
        return tic6x_match_ctrl_read_only;
    }
    abort();
}

static tic6x_operand_match
check_mem_deref(const tic6x_operand *op, unsigned int side)
{
    if (op->value.mem.mod != tic6x_mem_mod_none)
        return tic6x_match_bad_mem;
    if (op->value.mem.scaled != tic6x_offset_none)
        abort();
    if (op->value.mem.base_reg.side != side)
        return tic6x_match_bad_mem;
    return tic6x_match_matches;
}

static tic6x_operand_match
check_mem_short_ndw(const tic6x_operand *op, unsigned int side, tic6x_operand_form form)
{
    if (op->value.mem.base_reg.side != side)
        return tic6x_match_bad_mem;
    
    if (op->value.mem.mod == tic6x_mem_mod_none)
    {
        if (op->value.mem.scaled != tic6x_offset_none)
            abort();
        return tic6x_match_matches;
    }
    
    if (op->value.mem.scaled == tic6x_offset_none)
    {
        if (op->value.mem.mod == tic6x_mem_mod_plus || 
            op->value.mem.mod == tic6x_mem_mod_minus)
            abort();
        return tic6x_match_matches;
    }
    
    if (op->value.mem.offset_is_reg)
    {
        if (op->value.mem.scaled == tic6x_offset_unscaled && 
            form != tic6x_operand_mem_ndw)
            abort();
        return check_side_match(op->value.mem.offset.reg.side, side);
    }
    
    if (op->value.mem.offset.exp.X_op == O_constant)
        return tic6x_match_matches;
    return tic6x_match_bad_mem;
}

static tic6x_operand_match
check_mem_long_base(const tic6x_operand *op)
{
    if (op->value.mem.base_reg.side != 2)
        return tic6x_match_bad_mem;
    if (op->value.mem.base_reg.num != AREG_B14 && 
        op->value.mem.base_reg.num != AREG_B15)
        return tic6x_match_bad_mem;
    return tic6x_match_matches;
}

static tic6x_operand_match
check_mem_long_mod(const tic6x_operand *op)
{
    switch (op->value.mem.mod)
    {
    case tic6x_mem_mod_none:
        if (op->value.mem.scaled != tic6x_offset_none)
            abort();
        return tic6x_match_matches;
        
    case tic6x_mem_mod_plus:
        if (op->value.mem.scaled == tic6x_offset_none)
            abort();
        if (op->value.mem.offset_is_reg)
            return tic6x_match_bad_mem;
        if (op->value.mem.scaled == tic6x_offset_scaled && 
            op->value.mem.offset.exp.X_op != O_constant)
            return tic6x_match_bad_mem;
        return tic6x_match_matches;
        
    case tic6x_mem_mod_minus:
    case tic6x_mem_mod_preinc:
    case tic6x_mem_mod_predec:
    case tic6x_mem_mod_postinc:
    case tic6x_mem_mod_postdec:
        return tic6x_match_bad_mem;
        
    default:
        abort();
    }
}

static tic6x_operand_match
tic6x_operand_matches_form(const tic6x_operand *op, tic6x_operand_form form,
                          tic6x_rw rw, unsigned int side, unsigned int cross,
                          unsigned int data_side)
{
    unsigned int coarse = tic6x_coarse_operand_form(form);
    
    if (coarse != op->form)
        return tic6x_match_coarse;
    
    switch (form)
    {
    case tic6x_operand_asm_const:
        return (op->value.exp.X_op == O_constant) ? 
               tic6x_match_matches : tic6x_match_non_const;
        
    case tic6x_operand_link_const:
    case tic6x_operand_irp:
    case tic6x_operand_nrp:
    case tic6x_operand_func_unit:
        return tic6x_match_matches;
        
    case tic6x_operand_reg:
    case tic6x_operand_regpair:
        return check_side_match(op->value.reg.side, side);
        
    case tic6x_operand_xreg:
    case tic6x_operand_xregpair:
        return check_side_match(op->value.reg.side, cross);
        
    case tic6x_operand_dreg:
    case tic6x_operand_dregpair:
        return check_side_match(op->value.reg.side, data_side);
        
    case tic6x_operand_areg:
        return check_areg_validity(op, cross);
        
    case tic6x_operand_retreg:
        return check_retreg_validity(op, side);
        
    case tic6x_operand_ctrl:
        return check_ctrl_access(op, rw);
        
    case tic6x_operand_mem_deref:
        return check_mem_deref(op, side);
        
    case tic6x_operand_mem_short:
    case tic6x_operand_mem_ndw:
        return check_mem_short_ndw(op, side, form);
        
    case tic6x_operand_mem_long:
        {
            tic6x_operand_match base_result = check_mem_long_base(op);
            if (base_result != tic6x_match_matches)
                return base_result;
            return check_mem_long_mod(op);
        }
        
    default:
        abort();
    }
}

/* Return the number of bits shift used with DP-relative coding method
   CODING.  */

static unsigned int
tic6x_dpr_shift (tic6x_coding_method coding)
{
  switch (coding)
    {
    case tic6x_coding_ulcst_dpr_byte:
      return 0;

    case tic6x_coding_ulcst_dpr_half:
      return 1;

    case tic6x_coding_ulcst_dpr_word:
      return 2;

    default:
      abort ();
    }
}

/* Return the relocation used with DP-relative coding method
   CODING.  */

static bfd_reloc_code_real_type
tic6x_dpr_reloc (tic6x_coding_method coding)
{
  switch (coding)
    {
    case tic6x_coding_ulcst_dpr_byte:
      return BFD_RELOC_C6000_SBR_U15_B;

    case tic6x_coding_ulcst_dpr_half:
      return BFD_RELOC_C6000_SBR_U15_H;

    case tic6x_coding_ulcst_dpr_word:
      return BFD_RELOC_C6000_SBR_U15_W;

    default:
      abort ();
    }
}

/* Given a memory reference *MEM_REF as originally parsed, fill in
   defaults for missing offsets.  */

static void initialize_zero_offset(expressionS *exp)
{
    memset(exp, 0, sizeof(expressionS));
    exp->X_op = O_constant;
    exp->X_add_number = 0;
    exp->X_unsigned = 0;
}

static void initialize_unit_offset(expressionS *exp)
{
    memset(exp, 0, sizeof(expressionS));
    exp->X_op = O_constant;
    exp->X_add_number = 1;
    exp->X_unsigned = 0;
}

static void handle_mem_mod_none(tic6x_mem_ref *mem_ref)
{
    if (mem_ref->scaled != tic6x_offset_none)
        abort();
    
    mem_ref->mod = tic6x_mem_mod_plus;
    mem_ref->scaled = tic6x_offset_unscaled;
    mem_ref->offset_is_reg = false;
    initialize_zero_offset(&mem_ref->offset.exp);
}

static void handle_mem_mod_plus_minus(tic6x_mem_ref *mem_ref)
{
    if (mem_ref->scaled == tic6x_offset_none)
        abort();
}

static void handle_mem_mod_inc_dec(tic6x_mem_ref *mem_ref)
{
    if (mem_ref->scaled != tic6x_offset_none)
        return;
    
    mem_ref->scaled = tic6x_offset_scaled;
    mem_ref->offset_is_reg = false;
    initialize_unit_offset(&mem_ref->offset.exp);
}

static void tic6x_default_mem_ref(tic6x_mem_ref *mem_ref)
{
    switch (mem_ref->mod)
    {
    case tic6x_mem_mod_none:
        handle_mem_mod_none(mem_ref);
        break;

    case tic6x_mem_mod_plus:
    case tic6x_mem_mod_minus:
        handle_mem_mod_plus_minus(mem_ref);
        break;

    case tic6x_mem_mod_preinc:
    case tic6x_mem_mod_predec:
    case tic6x_mem_mod_postinc:
    case tic6x_mem_mod_postdec:
        handle_mem_mod_inc_dec(mem_ref);
        break;

    default:
        abort();
    }
}

/* Return the encoding in the 8-bit field of an SPMASK or SPMASKR
   instruction of the specified UNIT, side SIDE.  */

static unsigned int
tic6x_encode_spmask (tic6x_func_unit_base unit, unsigned int side)
{
  static const int unit_offsets[] = {
    [tic6x_func_unit_l] = -1,
    [tic6x_func_unit_s] = 1,
    [tic6x_func_unit_d] = 3,
    [tic6x_func_unit_m] = 5
  };

  if (unit >= sizeof(unit_offsets) / sizeof(unit_offsets[0]))
    abort ();

  return 1 << (side + unit_offsets[unit]);
}

/* Try to encode the instruction with opcode number ID and operands
   OPERANDS (number NUM_OPERANDS), creg value THIS_LINE_CREG and z
   value THIS_LINE_Z; FUNC_UNIT_SIDE, FUNC_UNIT_CROSS and
   FUNC_UNIT_DATA_SIDE describe the functional unit specification;
   SPLOOP_II is the ii value from the previous SPLOOP-family
   instruction, or 0 if not in such a loop; the only possible problems
   are operands being out of range (they already match the
   fine-grained form), and inappropriate predication.  If this
   succeeds, return the encoding and set *OK to true; otherwise return
   0 and set *OK to FALSE.  If a fix is needed, set *FIX_NEEDED to
   true and fill in *FIX_EXP, *FIX_PCREL, *FX_R_TYPE and *FIX_ADDA.
   Print error messages for failure if PRINT_ERRORS is true; the
   opcode starts at STR and has length OPC_LEN.  */

static unsigned int encode_fixed_fields(const tic6x_opcode *opct, const tic6x_insn_format *fmt)
{
    unsigned int opcode_value = fmt->cst_bits;
    unsigned int fld;

    for (fld = 0; fld < opct->num_fixed_fields; fld++)
    {
        if (opct->fixed_fields[fld].min_val == opct->fixed_fields[fld].max_val)
        {
            const tic6x_insn_field *fldd = tic6x_field_from_fmt(fmt, opct->fixed_fields[fld].field_id);
            if (fldd == NULL)
                abort();
            opcode_value |= opct->fixed_fields[fld].min_val << fldd->bitfields[0].low_pos;
        }
    }
    return opcode_value;
}

static bool check_constant_range(offsetT value, int width, bool is_signed, int opno, int opc_len, char *str, bool print_errors)
{
    if (is_signed)
    {
        if (value < -(1 << (width - 1)) || value >= (1 << (width - 1)))
        {
            if (print_errors)
                as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
            return false;
        }
    }
    else
    {
        if (value < 0 || value >= (1 << width))
        {
            if (print_errors)
                as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
            return false;
        }
    }
    return true;
}

static void setup_relocation(bool *fix_needed, expressionS **fix_exp, expressionS *exp, int *fix_pcrel, 
                            bfd_reloc_code_real_type *fx_r_type, bfd_reloc_code_real_type reloc_type, 
                            bool *fix_adda, bool adda_value)
{
    *fix_needed = true;
    *fix_exp = exp;
    *fix_pcrel = 0;
    *fx_r_type = reloc_type;
    *fix_adda = adda_value;
}

static unsigned int encode_signed_constant(offsetT sign_value, int width)
{
    unsigned int value = sign_value + (1 << (width - 1));
    return value ^ (1 << (width - 1));
}

static unsigned int encode_mem_mode(tic6x_mem_mod mod, bool offset_is_reg)
{
    unsigned int value;
    switch (mod)
    {
    case tic6x_mem_mod_plus:
        value = 1;
        break;
    case tic6x_mem_mod_minus:
        value = 0;
        break;
    case tic6x_mem_mod_preinc:
        value = 9;
        break;
    case tic6x_mem_mod_predec:
        value = 8;
        break;
    case tic6x_mem_mod_postinc:
        value = 11;
        break;
    case tic6x_mem_mod_postdec:
        value = 10;
        break;
    default:
        abort();
    }
    return value + (offset_is_reg ? 4 : 0);
}

static unsigned int calculate_fcyc_bits(int sploop_ii)
{
    if (sploop_ii <= 1)
        return 0;
    if (sploop_ii <= 2)
        return 1;
    if (sploop_ii <= 4)
        return 2;
    if (sploop_ii <= 8)
        return 3;
    if (sploop_ii <= 14)
        return 4;
    abort();
}

static unsigned int encode_fstg_value(unsigned int value, unsigned int fcyc_bits, int width)
{
    int i, t;
    for (t = 0, i = fcyc_bits; i < width; i++)
    {
        t = (t << 1) | (value & 1);
        value >>= 1;
    }
    return t << fcyc_bits;
}

static bfd_reloc_code_real_type get_pcrel_reloc_type(const tic6x_insn_field *fldd)
{
    if (fldd->bitfields[0].low_pos == 7 && fldd->bitfields[0].width == 21)
        return BFD_RELOC_C6000_PCR_S21;
    if (fldd->bitfields[0].low_pos == 16 && fldd->bitfields[0].width == 12)
        return BFD_RELOC_C6000_PCR_S12;
    if (fldd->bitfields[0].low_pos == 13 && fldd->bitfields[0].width == 10)
        return BFD_RELOC_C6000_PCR_S10;
    if (fldd->bitfields[0].low_pos == 16 && fldd->bitfields[0].width == 7)
        return BFD_RELOC_C6000_PCR_S7;
    abort();
}

static unsigned int encode_predication(const tic6x_insn_format *fmt, unsigned int this_line_creg, 
                                      unsigned int this_line_z, int opc_len, char *str, bool print_errors, bool *ok)
{
    const tic6x_insn_field *creg = tic6x_field_from_fmt(fmt, tic6x_field_creg);
    if (creg == NULL)
    {
        if (print_errors)
            as_bad(_("instruction '%.*s' cannot be predicated"), opc_len, str);
        *ok = false;
        return 0;
    }
    const tic6x_insn_field *z = tic6x_field_from_fmt(fmt, tic6x_field_z);
    if (z == NULL)
        abort();
    
    return (this_line_creg << creg->bitfields[0].low_pos) | (this_line_z << z->bitfields[0].low_pos);
}

static unsigned int
tic6x_try_encode(tic6x_opcode_id id, tic6x_operand *operands,
                unsigned int num_operands, unsigned int this_line_creg,
                unsigned int this_line_z, unsigned int func_unit_side,
                unsigned int func_unit_cross,
                unsigned int func_unit_data_side, int sploop_ii,
                expressionS **fix_exp, int *fix_pcrel,
                bfd_reloc_code_real_type *fx_r_type, bool *fix_adda,
                bool *fix_needed, bool *ok,
                bool print_errors, char *str, int opc_len)
{
    const tic6x_opcode *opct = &tic6x_opcode_table[id];
    const tic6x_insn_format *fmt = &tic6x_insn_format_table[opct->format];
    unsigned int opcode_value = encode_fixed_fields(opct, fmt);
    unsigned int fld;

    for (fld = 0; fld < opct->num_variable_fields; fld++)
    {
        const tic6x_insn_field *fldd = tic6x_field_from_fmt(fmt, opct->variable_fields[fld].field_id);
        if (fldd == NULL)
            abort();
        
        unsigned int opno = opct->variable_fields[fld].operand_num;
        unsigned int value = 0;
        expressionS ucexp;
        tic6x_mem_ref mem;

        switch (opct->variable_fields[fld].coding_method)
        {
        case tic6x_coding_ucst:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op != O_constant)
                abort();
            ucexp = operands[opno].value.exp;
            unsigned_constant:
            if (!check_constant_range(ucexp.X_add_number, fldd->bitfields[0].width, false, opno, opc_len, str, print_errors))
            {
                *ok = false;
                return 0;
            }
            value = ucexp.X_add_number;
            break;

        case tic6x_coding_scst:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op != O_constant)
            {
                value = 0;
                if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
                    abort();
                setup_relocation(fix_needed, fix_exp, &operands[opno].value.exp, fix_pcrel, 
                               fx_r_type, BFD_RELOC_C6000_ABS_S16, fix_adda, false);
                break;
            }
            offsetT sign_value = SEXT(operands[opno].value.exp.X_add_number);
            signed_constant:
            if (!check_constant_range(sign_value, fldd->bitfields[0].width, true, opno, opc_len, str, print_errors))
            {
                *ok = false;
                return 0;
            }
            value = encode_signed_constant(sign_value, fldd->bitfields[0].width);
            break;

        case tic6x_coding_ucst_minus_one:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op != O_constant)
                abort();
            if (operands[opno].value.exp.X_add_number <= 0 || 
                operands[opno].value.exp.X_add_number > (1 << fldd->bitfields[0].width))
            {
                if (print_errors)
                    as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                *ok = false;
                return 0;
            }
            value = operands[opno].value.exp.X_add_number - 1;
            break;

        case tic6x_coding_scst_negate:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op != O_constant)
                abort();
            sign_value = SEXT(-operands[opno].value.exp.X_add_number);
            goto signed_constant;

        case tic6x_coding_ulcst_dpr_byte:
        case tic6x_coding_ulcst_dpr_half:
        case tic6x_coding_ulcst_dpr_word:
            {
                unsigned int bits = tic6x_dpr_shift(opct->variable_fields[fld].coding_method);
                expressionS *expp;
                
                switch (operands[opno].form)
                {
                case TIC6X_OP_EXP:
                    if (operands[opno].value.exp.X_op == O_constant)
                    {
                        ucexp = operands[opno].value.exp;
                        goto unsigned_constant;
                    }
                    expp = &operands[opno].value.exp;
                    break;

                case TIC6X_OP_MEM_NOUNREG:
                    mem = operands[opno].value.mem;
                    tic6x_default_mem_ref(&mem);
                    if (mem.offset_is_reg)
                        abort();
                    if (mem.offset.exp.X_op == O_constant)
                    {
                        ucexp = mem.offset.exp;
                        if (mem.scaled == tic6x_offset_unscaled)
                        {
                            if (ucexp.X_add_number & ((1 << bits) - 1))
                            {
                                if (print_errors)
                                    as_bad(_("offset in operand %u of '%.*s' not divisible by %u"), 
                                         opno + 1, opc_len, str, 1u << bits);
                                *ok = false;
                                return 0;
                            }
                            ucexp.X_add_number >>= bits;
                        }
                        goto unsigned_constant;
                    }
                    if (mem.scaled != tic6x_offset_unscaled)
                        abort();
                    if (operands[opno].value.mem.mod == tic6x_mem_mod_none || 
                        operands[opno].value.mem.scaled != tic6x_offset_unscaled || 
                        operands[opno].value.mem.offset_is_reg)
                        abort();
                    expp = &operands[opno].value.mem.offset.exp;
                    break;

                default:
                    abort();
                }
                value = 0;
                if (fldd->bitfields[0].low_pos != 8 || fldd->bitfields[0].width != 15)
                    abort();
                setup_relocation(fix_needed, fix_exp, expp, fix_pcrel, fx_r_type, 
                               tic6x_dpr_reloc(opct->variable_fields[fld].coding_method), 
                               fix_adda, operands[opno].form == TIC6X_OP_EXP);
            }
            break;

        case tic6x_coding_lcst_low16:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op == O_constant)
                value = operands[opno].value.exp.X_add_number & 0xffff;
            else
            {
                value = 0;
                if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
                    abort();
                setup_relocation(fix_needed, fix_exp, &operands[opno].value.exp, fix_pcrel, 
                               fx_r_type, BFD_RELOC_C6000_ABS_L16, fix_adda, false);
            }
            break;

        case tic6x_coding_lcst_high16:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op == O_constant)
                value = (operands[opno].value.exp.X_add_number >> 16) & 0xffff;
            else
            {
                value = 0;
                if (fldd->bitfields[0].low_pos != 7 || fldd->bitfields[0].width != 16)
                    abort();
                setup_relocation(fix_needed, fix_exp, &operands[opno].value.exp, fix_pcrel, 
                               fx_r_type, BFD_RELOC_C6000_ABS_H16, fix_adda, false);
            }
            break;

        case tic6x_coding_pcrel:
        case tic6x_coding_pcrel_half:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            value = 0;
            *fix_needed = true;
            *fix_exp = &operands[opno].value.exp;
            *fix_pcrel = 1;
            *fx_r_type = get_pcrel_reloc_type(fldd);
            *fix_adda = false;
            break;

        case tic6x_coding_regpair_lsb:
            if (operands[opno].form != TIC6X_OP_REGPAIR)
                abort();
            value = operands[opno].value.reg.num;
            break;

        case tic6x_coding_regpair_msb:
            if (operands[opno].form != TIC6X_OP_REGPAIR)
                abort();
            value = operands[opno].value.reg.num + 1;
            break;

        case tic6x_coding_reg:
            switch (operands[opno].form)
            {
            case TIC6X_OP_REG:
            case TIC6X_OP_REGPAIR:
                value = operands[opno].value.reg.num;
                break;
            case TIC6X_OP_MEM_NOUNREG:
            case TIC6X_OP_MEM_UNREG:
                value = operands[opno].value.mem.base_reg.num;
                break;
            default:
                abort();
            }
            break;

        case tic6x_coding_areg:
            switch (operands[opno].form)
            {
            case TIC6X_OP_REG:
                value = (operands[opno].value.reg.num == 15 ? 1 : 0);
                break;
            case TIC6X_OP_MEM_NOUNREG:
                value = (operands[opno].value.mem.base_reg.num == 15 ? 1 : 0);
                break;
            default:
                abort();
            }
            break;

        case tic6x_coding_crlo:
            if (operands[opno].form != TIC6X_OP_CTRL)
                abort();
            value = tic6x_ctrl_table[operands[opno].value.ctrl].crlo;
            break;

        case tic6x_coding_crhi:
            if (operands[opno].form != TIC6X_OP_CTRL)
                abort();
            value = 0;
            break;

        case tic6x_coding_reg_shift:
            if (operands[opno].form != TIC6X_OP_REGPAIR)
                abort();
            value = operands[opno].value.reg.num >> 1;
            break;

        case tic6x_coding_mem_offset:
            if (operands[opno].form != TIC6X_OP_MEM_NOUNREG)
                abort();
            mem = operands[opno].value.mem;
            tic6x_default_mem_ref(&mem);
            if (mem.offset_is_reg)
            {
                if (mem.scaled != tic6x_offset_scaled)
                    abort();
                value = mem.offset.reg.num;
            }
            else
            {
                int scale;
                if (mem.offset.exp.X_op != O_constant)
                    abort();
                switch (mem.scaled)
                {
                case tic6x_offset_scaled:
                    scale = 1;
                    break;
                case tic6x_offset_unscaled:
                    scale = opct->operand_info[opno].size;
                    if (scale != 1 && scale != 2 && scale != 4 && scale != 8)
                        abort();
                    break;
                default:
                    abort();
                }
                if (mem.offset.exp.X_add_number < 0 || 
                    mem.offset.exp.X_add_number >= (1 << fldd->bitfields[0].width) * scale)
                {
                    if (print_errors)
                        as_bad(_("offset in operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                    *ok = false;
                    return 0;
                }
                if (mem.offset.exp.X_add_number % scale)
                {
                    if (print_errors)
                        as_bad(_("offset in operand %u of '%.*s' not divisible by %u"), 
                             opno + 1, opc_len, str, scale);
                    *ok = false;
                    return 0;
                }
                value = mem.offset.exp.X_add_number / scale;
            }
            break;

        case tic6x_coding_mem_offset_noscale:
            if (operands[opno].form != TIC6X_OP_MEM_UNREG)
                abort();
            mem = operands[opno].value.mem;
            tic6x_default_mem_ref(&mem);
            if (mem.offset_is_reg)
                value = mem.offset.reg.num;
            else
            {
                if (mem.offset.exp.X_op != O_constant)
                    abort();
                if (mem.offset.exp.X_add_number < 0 || 
                    mem.offset.exp.X_add_number >= (1 << fldd->bitfields[0].width))
                {
                    if (print_errors)
                        as_bad(_("offset in operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                    *ok = false;
                    return 0;
                }
                value = mem.offset.exp.X_add_number;
            }
            break;

        case tic6x_coding_mem_mode:
            if (operands[opno].form != TIC6X_OP_MEM_NOUNREG && operands[opno].form != TIC6X_OP_MEM_UNREG)
                abort();
            mem = operands[opno].value.mem;
            tic6x_default_mem_ref(&mem);
            value = encode_mem_mode(mem.mod, mem.offset_is_reg);
            break;

        case tic6x_coding_scaled:
            if (operands[opno].form != TIC6X_OP_MEM_UNREG)
                abort();
            mem = operands[opno].value.mem;
            tic6x_default_mem_ref(&mem);
            value = (mem.scaled == tic6x_offset_scaled) ? 1 : 0;
            break;

        case tic6x_coding_spmask:
            if (fldd->bitfields[0].low_pos != 18)
                abort();
            value = 0;
            for (opno = 0; opno < num_operands; opno++)
            {
                unsigned int v = tic6x_encode_spmask(operands[opno].value.func_unit.base,
                                                    operands[opno].value.func_unit.side);
                if (value & v)
                {
                    if (print_errors)
                        as_bad(_("functional unit already masked for operand %u of '%.*s'"), 
                             opno + 1, opc_len, str);
                    *ok = false;
                    return 0;
                }
                value |= v;
            }
            break;

        case tic6x_coding_reg_unused:
            value = 0;
            break;

        case tic6x_coding_fstg:
        case tic6x_coding_fcyc:
            if (operands[opno].form != TIC6X_OP_EXP)
                abort();
            if (operands[opno].value.exp.X_op != O_constant)
                abort();
            if (!sploop_ii)
            {
                if (print_errors)
                    as_bad(_("'%.*s' instruction not in a software pipelined loop"), opc_len, str);
                *ok = false;
                return 0;
            }

            unsigned int fcyc_bits = calculate_fcyc_bits(sploop_ii);
            if (fcyc_bits > fldd->bitfields[0].width)
                abort();

            if (opct->variable_fields[fld].coding_method == tic6x_coding_fstg)
            {
                if (operands[opno].value.exp.X_add_number < 0 || 
                    operands[opno].value.exp.X_add_number >= (1 << (fldd->bitfields[0].width - fcyc_bits)))
                {
                    if (print_errors)
                        as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                    *ok = false;
                    return 0;
                }
                value = encode_fstg_value(operands[opno].value.exp.X_add_number, fcyc_bits, 
                                        fldd->bitfields[0].width);
            }
            else
            {
                if (operands[opno].value.exp.X_add_number < 0 || 
                    operands[opno].value.exp.X_add_number >= sploop_ii)
                {
                    if (print_errors)
                        as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                    *ok = false;
                    return 0;
                }
                value = operands[opno].value.exp.X_add_number;
            }
            break;

        case tic6x_coding_fu:
            value = func_unit_side == 2 ? 1 : 0;
            break;

        case tic6x_coding_data_fu:
            value = func_unit_data_side == 2 ? 1 : 0;
            break;

        case tic6x_coding_xpath:
            value = func_unit_cross;
            break;

        default:
            abort();
        }

        unsigned int ffld;
        for (ffld = 0; ffld < opct->num_fixed_fields; ffld++)
        {
            if (opct->fixed_fields[ffld].field_id == opct->variable_fields[fld].field_id && 
                (value < opct->fixed_fields[ffld].min_val || value > opct->fixed_fields[ffld].max_val))
            {
                if (print_errors)
                    as_bad(_("operand %u of '%.*s' out of range"), opno + 1, opc_len, str);
                *ok = false;
                return 0;
            }
        }

        opcode_value |= value << fldd->bitfields[0].low_pos;
    }

    if (this_line_creg)
    {
        unsigned int pred_value = encode_predication(fmt, this_line_creg, this_line_z, opc_len, str, print_errors, ok);
        if (!*ok)
            return 0;
        opcode_value |= pred_value;
    }

    *ok = true;
    return opcode_value;
}

/* Convert the target integer stored in N bytes in BUF to a host
   integer, returning that value.  */

static valueT
md_chars_to_number (char *buf, int n)
{
  valueT result = 0;
  const int BYTE_SHIFT = 8;
  const unsigned char BYTE_MASK = 0xff;

  while (n--)
  {
    result <<= BYTE_SHIFT;
    int index = target_big_endian ? 0 : n;
    result |= (buf[index] & BYTE_MASK);
    if (target_big_endian)
      buf++;
  }

  return result;
}

/* Assemble the instruction starting at STR (an opcode, with the
   opcode name all-lowercase).  */

#define OPCODE_HASH_LOOKUP_FAILED(opc_list, str, p, opc_len) do { \
    if (opc_list == NULL) { \
        char c = *p; \
        *p = 0; \
        as_bad(_("unknown opcode '%s'"), str); \
        *p = c; \
        return; \
    } \
} while (0)

#define REPORT_UNSUPPORTED_INSTRUCTION(ok_arch, ok_fu, ok_arch_fu, opc_len, str, opcm) do { \
    if (!ok_arch) { \
        as_bad(_("'%.*s' instruction not supported on this architecture"), opc_len, str); \
        free(opcm); \
        return; \
    } \
    if (!ok_fu) { \
        as_bad(_("'%.*s' instruction not supported on this functional unit"), opc_len, str); \
        free(opcm); \
        return; \
    } \
    if (!ok_arch_fu) { \
        as_bad(_("'%.*s' instruction not supported on this functional unit for this architecture"), opc_len, str); \
        free(opcm); \
        return; \
    } \
} while (0)

static void initialize_line_state(bool *this_line_parallel, bool *this_line_spmask,
                                   unsigned int *this_line_creg, unsigned int *this_line_z,
                                   tic6x_label_list **this_insn_label_list,
                                   segment_info_type *seginfo)
{
    *this_line_parallel = tic6x_line_parallel;
    *this_line_spmask = tic6x_line_spmask;
    *this_line_creg = tic6x_line_creg;
    *this_line_z = tic6x_line_z;
    tic6x_line_parallel = false;
    tic6x_line_spmask = false;
    tic6x_line_creg = 0;
    tic6x_line_z = 0;
    *this_insn_label_list = seginfo->tc_segment_info_data.label_list;
    seginfo->tc_segment_info_data.label_list = NULL;
}

static void parse_func_unit(char **p, tic6x_func_unit_base *func_unit_base,
                             unsigned int *func_unit_side, unsigned int *func_unit_cross,
                             unsigned int *cross_side, unsigned int *func_unit_data_side)
{
    if (**p != '.')
        return;

    bool good_func_unit;
    tic6x_func_unit_base maybe_base = tic6x_func_unit_nfu;
    unsigned int maybe_side = 0;
    unsigned int maybe_cross = 0;
    unsigned int maybe_data_side = 0;

    good_func_unit = tic6x_parse_func_unit_base(*p + 1, &maybe_base, &maybe_side);

    if (good_func_unit) {
        if (is_whitespace((*p)[3]) || is_end_of_stmt((*p)[3])) {
            *p += 3;
        } else if (((*p)[3] == 'x' || (*p)[3] == 'X') &&
                   (is_whitespace((*p)[4]) || is_end_of_stmt((*p)[4]))) {
            maybe_cross = 1;
            *p += 4;
        } else if (maybe_base == tic6x_func_unit_d &&
                   ((*p)[3] == 't' || (*p)[3] == 'T') &&
                   ((*p)[4] == '1' || (*p)[4] == '2') &&
                   (is_whitespace((*p)[5]) || is_end_of_stmt((*p)[5]))) {
            maybe_data_side = (*p)[4] - '0';
            *p += 5;
        } else {
            good_func_unit = false;
        }
    }

    if (good_func_unit) {
        *func_unit_base = maybe_base;
        *func_unit_side = maybe_side;
        *func_unit_cross = maybe_cross;
        *cross_side = (*func_unit_cross ? 3 - *func_unit_side : *func_unit_side);
        *func_unit_data_side = maybe_data_side;
    }

    skip_whitespace(*p);
}

static bool check_opcode_architecture(const tic6x_opcode *opcode)
{
    return (opcode->isa_variants & tic6x_features) != 0;
}

static bool check_opcode_func_unit(const tic6x_opcode *opcode,
                                    tic6x_func_unit_base func_unit_base,
                                    unsigned int func_unit_side,
                                    unsigned int func_unit_cross,
                                    unsigned int func_unit_data_side)
{
    if (opcode->func_unit != func_unit_base)
        return false;
    if (func_unit_side == 1 && (opcode->flags & TIC6X_FLAG_SIDE_B_ONLY))
        return false;
    if (func_unit_cross && (opcode->flags & TIC6X_FLAG_NO_CROSS))
        return false;
    if (!func_unit_data_side && (opcode->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
        return false;
    if (func_unit_data_side && !(opcode->flags & (TIC6X_FLAG_LOAD | TIC6X_FLAG_STORE)))
        return false;
    if (func_unit_data_side == 1 && (opcode->flags & TIC6X_FLAG_SIDE_T2_ONLY))
        return false;
    return true;
}

static void process_spmask_operands(const tic6x_opcode *opcode,
                                     unsigned int *operand_forms,
                                     bool *num_operands_permitted,
                                     unsigned int *num_operands)
{
    if (!(opcode->flags & TIC6X_FLAG_SPMASK))
        return;

    if (*num_operands != 1 || opcode->operand_info[0].form != tic6x_operand_func_unit)
        abort();

    *num_operands = 8;
    for (unsigned int i = 0; i < *num_operands; i++) {
        operand_forms[i] |= tic6x_coarse_operand_form(tic6x_operand_func_unit);
        num_operands_permitted[i] = true;
    }
}

static void process_regular_operands(const tic6x_opcode *opcode,
                                      unsigned int *operand_forms,
                                      unsigned int num_operands)
{
    for (unsigned int i = 0; i < num_operands; i++) {
        tic6x_operand_form f = opcode->operand_info[i].form;
        operand_forms[i] |= tic6x_coarse_operand_form(f);
    }
}

static void report_operand_error(tic6x_operand_match fine_failure,
                                  unsigned int operand_index,
                                  int opc_len, char *str)
{
    const char *error_msg;
    switch (fine_failure) {
        case tic6x_match_non_const:
            error_msg = "operand %u of '%.*s' not constant";
            break;
        case tic6x_match_wrong_side:
            error_msg = "operand %u of '%.*s' on wrong side";
            break;
        case tic6x_match_bad_return:
            error_msg = "operand %u of '%.*s' not a valid return address register";
            break;
        case tic6x_match_ctrl_write_only:
            error_msg = "operand %u of '%.*s' is write-only";
            break;
        case tic6x_match_ctrl_read_only:
            error_msg = "operand %u of '%.*s' is read-only";
            break;
        case tic6x_match_bad_mem:
            error_msg = "operand %u of '%.*s' not a valid memory reference";
            break;
        case tic6x_match_bad_address:
            error_msg = "operand %u of '%.*s' not a valid base address register";
            break;
        default:
            abort();
    }
    as_bad(_(error_msg), operand_index + 1, opc_len, str);
}

static bool validate_single_operand(unsigned int operand_index,
                                     tic6x_operand *operands,
                                     tic6x_opcode_id *opcm,
                                     unsigned int num_matching_opcodes,
                                     unsigned int num_operands_read,
                                     unsigned int func_unit_side,
                                     unsigned int cross_side,
                                     unsigned int func_unit_data_side,
                                     int opc_len, char *str)
{
    bool coarse_ok = false;
    bool fine_ok = false;
    tic6x_operand_match fine_failure = tic6x_match_matches;

    for (unsigned int j = 0; j < num_matching_opcodes; j++) {
        tic6x_operand_form f;
        tic6x_rw rw;
        unsigned int cf;
        tic6x_operand_match this_fine_failure;

        if (tic6x_opcode_table[opcm[j]].flags & TIC6X_FLAG_SPMASK) {
            f = tic6x_operand_func_unit;
            rw = tic6x_rw_none;
        } else {
            if (tic6x_opcode_table[opcm[j]].num_operands != num_operands_read)
                continue;
            f = tic6x_opcode_table[opcm[j]].operand_info[operand_index].form;
            rw = tic6x_opcode_table[opcm[j]].operand_info[operand_index].rw;
        }
        cf = tic6x_coarse_operand_form(f);

        if (operands[operand_index].form != cf)
            continue;

        coarse_ok = true;
        this_fine_failure = tic6x_operand_matches_form(&operands[operand_index], f, rw,
                                                        func_unit_side, cross_side,
                                                        func_unit_data_side);
        if (this_fine_failure == tic6x_match_matches) {
            fine_ok = true;
            break;
        }
        if (fine_failure == tic6x_match_matches || fine_failure > this_fine_failure)
            fine_failure = this_fine_failure;
    }

    if (!coarse_ok)
        abort();

    if (!fine_ok) {
        report_operand_error(fine_failure, operand_index, opc_len, str);
        return false;
    }
    return true;
}

static bool find_matching_opcode(tic6x_opcode_id *opcm,
                                  unsigned int num_matching_opcodes,
                                  tic6x_operand *operands,
                                  unsigned int num_operands_read,
                                  unsigned int func_unit_side,
                                  unsigned int cross_side,
                                  unsigned int func_unit_data_side,
                                  unsigned int *opc_rank,
                                  int *min_rank, int *max_rank)
{
    bool found_match = false;

    for (unsigned int i = 0; i < num_matching_opcodes; i++) {
        bool this_matches = true;

        if (!(tic6x_opcode_table[opcm[i]].flags & TIC6X_FLAG_SPMASK) &&
            tic6x_opcode_table[opcm[i]].num_operands != num_operands_read)
            continue;

        for (unsigned int j = 0; j < num_operands_read; j++) {
            tic6x_operand_form f;
            tic6x_rw rw;

            if (tic6x_opcode_table[opcm[i]].flags & TIC6X_FLAG_SPMASK) {
                f = tic6x_operand_func_unit;
                rw = tic6x_rw_none;
            } else {
                f = tic6x_opcode_table[opcm[i]].operand_info[j].form;
                rw = tic6x_opcode_table[opcm[i]].operand_info[j].rw;
            }
            if (tic6x_operand_matches_form(&operands[j], f, rw, func_unit_side,
                                            cross_side, func_unit_data_side) != tic6x_match_matches) {
                this_matches = false;
                break;
            }
        }

        if (this_matches) {
            int rank = TIC6X_PREFER_VAL(tic6x_opcode_table[opcm[i]].flags);
            if (rank < *min_rank)
                *min_rank = rank;
            if (rank > *max_rank)
                *max_rank = rank;
            if (opc_rank[rank] == -1u)
                opc_rank[rank] = i;
            else
                abort();
            found_match = true;
        }
    }
    return found_match;
}

static void handle_parallel_instruction(segment_info_type *seginfo,
                                         tic6x_label_list *this_insn_label_list,
                                         const tic6x_opcode *opct,
                                         int opc_len, char *str,
                                         fragS **insn_frag, char **output)
{
    *insn_frag = seginfo->tc_segment_info_data.execute_packet_frag;
    if (*insn_frag == NULL) {
        as_bad(_("parallel instruction not following another instruction"));
        return;
    }
    if ((*insn_frag)->fr_fix >= 32) {
        as_bad(_("too many instructions in execute packet"));
        return;
    }
    if (this_insn_label_list != NULL)
        as_bad(_("label not at start of execute packet"));
    if (opct->flags & TIC6X_FLAG_FIRST)
        as_bad(_("'%.*s' instruction not at start of execute packet"), opc_len, str);
    *seginfo->tc_segment_info_data.last_insn_lsb |= 0x1;
    *output = (*insn_frag)->fr_literal + (*insn_frag)->fr_fix;
}

static void handle_non_parallel_instruction(segment_info_type *seginfo,
                                             tic6x_label_list *this_insn_label_list,
                                             fragS **insn_frag, char **output)
{
    tic6x_label_list *l;
    seginfo->tc_segment_info_data.spmask_addr = NULL;
    seginfo->tc_segment_info_data.func_units_used = 0;

    if (frag_now_fix() != 0) {
        if (frag_now->fr_type != rs_machine_dependent)
            frag_wane(frag_now);
        frag_new(0);
    }
    frag_grow(32);
    *insn_frag = seginfo->tc_segment_info_data.execute_packet_frag = frag_now;
    for (l = this_insn_label_list; l; l = l->next) {
        symbol_set_frag(l->label, frag_now);
        S_SET_VALUE(l->label, 0);
        S_SET_SEGMENT(l->label, now_seg);
    }
    tic6x_free_label_list(this_insn_label_list);
    dwarf2_emit_insn(0);
    *output = frag_var(rs_machine_dependent, 32, 32, 0, NULL, 0, NULL);
    if (*output != (*insn_frag)->fr_literal)
        abort();
    (*insn_frag)->tc_frag_data.is_insns = true;
    (*insn_frag)->tc_frag_data.can_cross_fp_boundary = tic6x_can_cross_fp_boundary;
}

static void check_func_unit_usage(segment_info_type *seginfo,
                                   tic6x_func_unit_base func_unit_base,
                                   unsigned int func_unit_side)
{
    if (func_unit_base == tic6x_func_unit_nfu)
        return;

    unsigned int func_unit_enc = tic6x_encode_spmask(func_unit_base, func_unit_side);
    if (seginfo->tc_segment_info_data.func_units_used & func_unit_enc)
        as_bad(_("functional unit already used in this execute packet"));
    seginfo->tc_segment_info_data.func_units_used |= func_unit_enc;
}

static void handle_sploop_instructions(const tic6x_opcode *opct,
                                        segment_info_type *seginfo,
                                        tic6x_operand *operands,
                                        unsigned int num_operands_read,
                                        int opc_len, char *str)
{
    if (opct->flags & TIC6X_FLAG_SPLOOP) {
        if (seginfo->tc_segment_info_data.sploop_ii)
            as_bad(_("nested software pipelined loop"));
        if (num_operands_read != 1 || operands[0].form != TIC6X_OP_EXP ||
            operands[0].value.exp.X_op != O_constant)
            abort();
        seginfo->tc_segment_info_data.sploop_ii = operands[0].value.exp.X_add_number;
    } else if (opct->flags & TIC6X_FLAG_SPKERNEL) {
        if (!seginfo->tc_segment_info_data.sploop_ii)
            as_bad(_("'%.*s' instruction not in a software pipelined loop"), opc_len, str);
        seginfo->tc_segment_info_data.sploop_ii = 0;
    }
}

static void handle_spmask(segment_info_type *seginfo,
                           bool this_line_spmask,
                           tic6x_func_unit_base func_unit_base,
                           unsigned int func_unit_side)
{
    if (!this_line_spmask)
        return;

    if (seginfo->tc_segment_info_data.spmask_addr == NULL) {
        as_bad(_("'||^' without previous SPMASK"));
    } else if (func_unit_base == tic6x_func_unit_nfu) {
        as_bad(_("cannot mask instruction using no functional unit"));
    } else {
        unsigned int spmask_opcode = md_chars_to_number(seginfo->tc_segment_info_data.spmask_addr, 4);
        unsigned int mask_bit = tic6x_encode_spmask(func_unit_base, func_unit_side);
        mask_bit <<= 18;
        if (spmask_opcode & mask_bit)
            as_bad(_("functional unit already masked"));
        spmask_opcode |= mask_bit;
        md_number_to_chars(seginfo->tc_segment_info_data.spmask_addr, spmask_opcode, 4);
    }
}

void md_assemble(char *str)
{
    char *p;
    int opc_len;
    bool this_line_parallel;
    bool this_line_spmask;
    unsigned int this_line_creg;
    unsigned int this_line_z;
    tic6x_label_list *this_insn_label_list;
    segment_info_type *seginfo;
    tic6x_opcode_list *opc_list, *opc;
    tic6x_func_unit_base func_unit_base = tic6x_func_unit_nfu;
    unsigned int func_unit_side = 0;
    unsigned int func_unit_cross = 0;
    unsigned int cross_side = 0;
    unsigned int func_unit_data_side = 0;
    unsigned int max_matching_opcodes, num_matching_opcodes;
    tic6x_opcode_id *opcm = NULL;
    unsigned int opc_rank[TIC6X_NUM_PREFER];
    const tic6x_opcode *opct = NULL;
    int min_rank, try_rank, max_rank;
    bool num_operands_permitted[TIC6X_MAX_SOURCE_OPERANDS + 1] = { false };
    unsigned int operand_forms[TIC6X_MAX_SOURCE_OPERANDS] = { 0 };
    tic6x_operand operands[TIC6X_MAX_SOURCE_OPERANDS];
    unsigned int max_num_operands;
    unsigned int num_operands_read;
    bool ok_this_arch, ok_this_fu, ok_this_arch_fu;
    bool bad_operands = false;
    unsigned int opcode_value;
    bool encoded_ok;
    bool fix_needed = false;
    expressionS *fix_exp = NULL;
    int fix_pcrel = 0;
    bfd_reloc_code_real_type fx_r_type = BFD_RELOC_UNUSED;
    bool fix_adda = false;
    fragS *insn_frag;
    char *output;

    p = str;
    while (!is_end_of_stmt(*p) && !is_whitespace(*p))
        p++;

    if (p == str)
        abort();

    tic6x_seen_insns = true;
    if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
        tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;

    seginfo = seg_info(now_seg);
    initialize_line_state(&this_line_parallel, &this_line_spmask,
                           &this_line_creg, &this_line_z,
                           &this_insn_label_list, seginfo);

    opc_list = str_hash_find_n(opcode_hash, str, p - str);
    OPCODE_HASH_LOOKUP_FAILED(opc_list, str, p, p - str);

    opc_len = p - str;
    skip_whitespace(p);

    parse_func_unit(&p, &func_unit_base, &func_unit_side,
                     &func_unit_cross, &cross_side, &func_unit_data_side);

    max_matching_opcodes = 0;
    for (opc = opc_list; opc; opc = opc->next)
        max_matching_opcodes++;
    num_matching_opcodes = 0;
    opcm = XNEWVEC(tic6x_opcode_id, max_matching_opcodes);
    max_num_operands = 0;
    ok_this_arch = false;
    ok_this_fu = false;
    ok_this_arch_fu = false;

    for (opc = opc_list; opc; opc = opc->next) {
        unsigned int num_operands;
        bool this_opc_arch_ok = true;
        bool this_opc_fu_ok = true;

        if (tic6x_insn_format_table[tic6x_opcode_table[opc->id].format].num_bits != 32)
            continue;

        this_opc_arch_ok = check_opcode_architecture(&tic6x_opcode_table[opc->id]);
        this_opc_fu_ok = check_opcode_func_unit(&tic6x_opcode_table[opc->id],
                                                 func_unit_base, func_unit_side,
                                                 func_unit_cross, func_unit_data_side);

        if (this_opc_arch_ok)
            ok_this_arch = true;
        if (this_opc_fu_ok)
            ok_this_fu = true;
        if (!this_opc_arch_ok || !this_opc_fu_ok)
            continue;

        ok_this_arch_fu = true;
        opcm[num_matching_opcodes] = opc->id;
        num_matching_opcodes++;
        num_operands = tic6x_opcode_table[opc->id].num_operands;

        process_spmask_operands(&tic6x_opcode_table[opc->id], operand_forms,
                                 num_operands_permitted, &num_operands);
        if (!(tic6x_opcode_table[opc->id].flags & TIC6X_FLAG_SPMASK))
            process_regular_operands(&tic6x_opcode_table[opc->id], operand_forms, num_operands);

        num_operands_permitted[num_operands] = true;
        if (num_operands > max_num_operands)
            max_num_operands = num_operands;
    }

    REPORT_UNSUPPORTED_INSTRUCTION(ok_this_arch, ok_this_fu, ok_this_arch_fu, opc_len, str, opcm);

    if (num_matching_opcodes == 0)
        abort();

    num_operands_read = 0;
    while (true) {
        skip_whitespace(p);
        if (is_end_of_stmt(*p)) {
            if (num_operands_read > 0) {
                as_bad(_("missing operand after comma"));
                bad_operands = true;
            }
            break;
        }

        if (max_num_operands == 0) {
            as_bad(_("too many operands to '%.*s'"), opc_len, str);
            bad_operands = true;
            break;
        }

        if (!tic6x_parse_operand(&p, &operands[num_operands_read],
                                  operand_forms[num_operands_read], str, opc_len,
                                  num_operands_read + 1))
            bad_operands = true;
        num_operands_read++;

        if (is_end_of_stmt(*p))
            break;
        else if (*p == ',') {
            p++;
            if (num_operands_read == max_num_operands) {
                as_bad(_("too many operands to '%.*s'"), opc_len, str);
                bad_operands = true;
                break;
            }
            continue;
        } else
            abort();
    }

    if (!bad_operands && !num_operands_permitted[num_operands_read]) {
        as_bad(_("bad number of operands to '%.*s'"), opc_len, str);
        bad_operands = true;
    }

    if (!bad_operands) {
        for (unsigned int i = 0; i < num_operands_read; i++) {
            if (!validate_single_operand(i, operands, opcm, num_matching_opcodes,
                                          num_operands_read, func_unit_side,
                                          cross_side, func_unit_data_side,
                                          opc_len, str)) {
                bad_operands = true;
                break;
            }
        }
    }

    if (!bad_operands) {
        for (unsigned int i = 0; i < TIC6X_NUM_PREFER; i++)
            opc_rank[i] = -1u;
        min_rank = TIC6X_NUM_PREFER - 1;
        max_rank = 0;

        if (!find_matching_opcode(opcm, num_matching_opcodes, operands,
                                   num_operands_read, func_unit_side,
                                   cross_side, func_unit_data_side,
                                   opc_rank, &min_rank, &max_rank)) {
            as_bad(_("bad operand combination for '%.*s'"), opc_len, str);
            bad_operands = true;
        }
    }

    if (bad_operands) {
        free(opcm);
        return;
    }

    opcode_value = 0;
    encoded_ok = false;
    for (try_rank = max_rank; try_rank >= min_rank; try_rank--) {
        fix_needed = false;
        if (opc_rank[try_rank] == -1u)
            continue;

        opcode_value = tic6x_try_encode(opcm[opc_rank[try_rank]], operands,
                                         num_operands_read, this_line_creg,
                                         this_line_z, func_unit_side,
                                         func_unit_cross, func_unit_data_side,
                                         seginfo->tc_segment_info_data.sploop_ii,
                                         &fix_exp, &fix_pcrel, &fx_r_type,
                                         &fix_adda, &fix_needed, &encoded_ok,
                                         try_rank == min_rank, str, opc_len);
        if (encoded_ok) {
            opct = &tic6x_opcode_table[opcm[opc_rank[try_rank]]];
            break;
        }
    }

    free(opcm);

    if (!encoded_ok)
        return;

    if (this_line_parallel) {
        handle_parallel_instruction(seginfo, this_insn_label_list, opct,
                                     opc_len, str, &insn_frag, &output);
    } else {
        handle_non_parallel_instruction(seginfo, this_insn_label_list,
                                         &insn_frag, &output);
    }

    check_func_unit_usage(seginfo, func_unit_base, func_unit_side);
    handle_sploop_instructions(opct, seginfo, operands, num_operands_read, opc_len, str);
    handle_spmask(seginfo, this_line_spmask, func_unit_base, func_unit_side);

    record_alignment(now_seg, 5);
    md_number_to_chars(output, opcode_value, 4);
    if (fix_needed)
        tic6x_fix_new_exp(insn_frag, output - insn_frag->fr_literal, 4, fix_exp,
                           fix_pcrel, fx_r_type, fix_adda);
    insn_frag->fr_fix += 4;
    insn_frag->fr_var -= 4;
    seginfo->tc_segment_info_data.last_insn_lsb = (target_big_endian ? output + 3 : output);
    if (opct->flags & TIC6X_FLAG_SPMASK)
        seginfo->tc_segment_info_data.spmask_addr = output;
}

/* Modify NEWVAL (32-bit) by inserting VALUE, shifted right by SHIFT
   and the least significant BITS bits taken, at position POS.  */
#define MODIFY_VALUE(NEWVAL, VALUE, SHIFT, POS, BITS)			\
  do {									\
    (NEWVAL) &= 0xffffffffU & ~(((1U << (BITS)) - 1) << (POS));		\
    (NEWVAL) |= (((VALUE) >> (SHIFT)) & ((1U << (BITS)) - 1)) << (POS);	\
  } while (0)

/* Apply a fixup to the object file.  */

void
md_apply_fix (fixS *fixP, valueT *valP, segT seg ATTRIBUTE_UNUSED)
{
  valueT value = *valP;
  char *buf = fixP->fx_where + fixP->fx_frag->fr_literal;

  value = SEXT (value);
  *valP = value;

  fixP->fx_offset = SEXT (fixP->fx_offset);

  if (fixP->fx_addsy == NULL && fixP->fx_pcrel == 0)
    fixP->fx_done = 1;

  fixP->fx_no_overflow = 1;

  switch (fixP->fx_r_type)
    {
    case BFD_RELOC_NONE:
    case BFD_RELOC_C6000_EHTYPE:
      fixP->fx_done = 0;
      break;

    case BFD_RELOC_32:
      if (fixP->fx_done || !seg->use_rela_p)
	md_number_to_chars (buf, value, 4);
      break;

    case BFD_RELOC_16:
      handle_reloc_16 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_8:
      handle_reloc_8 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_ABS_S16:
    case BFD_RELOC_C6000_ABS_L16:
    case BFD_RELOC_C6000_SBR_S16:
    case BFD_RELOC_C6000_SBR_L16_B:
    case BFD_RELOC_C6000_SBR_L16_H:
    case BFD_RELOC_C6000_SBR_L16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
      handle_sbr_l16_relocs (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_ABS_H16:
    case BFD_RELOC_C6000_SBR_H16_B:
    case BFD_RELOC_C6000_SBR_H16_H:
    case BFD_RELOC_C6000_SBR_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
      handle_sbr_h16_relocs (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_PCR_H16:
    case BFD_RELOC_C6000_PCR_L16:
      handle_pcr_16_relocs (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_SBR_U15_B:
      handle_sbr_u15_b (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_SBR_U15_H:
      handle_sbr_u15_h (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_SBR_U15_W:
    case BFD_RELOC_C6000_SBR_GOT_U15_W:
      handle_sbr_u15_w (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_DSBT_INDEX:
      handle_dsbt_index (fixP, value);
      break;

    case BFD_RELOC_C6000_PCR_S21:
      handle_pcr_s21 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_PCR_S12:
      handle_pcr_s12 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_PCR_S10:
      handle_pcr_s10 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_PCR_S7:
      handle_pcr_s7 (fixP, seg, buf, value);
      break;

    case BFD_RELOC_C6000_PREL31:
      fixP->fx_done = 0;
      break;

    default:
      abort ();
    }
}

#define MAX_16BIT_VALUE 0xffff
#define MAX_8BIT_VALUE 0xff
#define SIGNED_16BIT_OFFSET 0x8000
#define SIGNED_8BIT_OFFSET 0x80
#define ALIGNMENT_2BYTE 1
#define ALIGNMENT_4BYTE 3
#define PCR_S21_RANGE 0x400000
#define PCR_S21_MAX 0x3ffffc
#define PCR_S12_RANGE 0x2000
#define PCR_S12_MAX 0x1ffc
#define PCR_S10_RANGE 0x800
#define PCR_S10_MAX 0x7fc
#define PCR_S7_RANGE 0x100
#define PCR_S7_MAX 0xfc
#define SBR_U15_MAX 0x7fff
#define SBR_U15_H_MAX 0xfffe
#define SBR_U15_W_MAX 0x1fffc

static void
handle_reloc_16 (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      if (value + SIGNED_16BIT_OFFSET > MAX_16BIT_VALUE + SIGNED_16BIT_OFFSET)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("value too large for 2-byte field"));
      md_number_to_chars (buf, value, 2);
    }
}

static void
handle_reloc_8 (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      if (value + SIGNED_8BIT_OFFSET > MAX_8BIT_VALUE + SIGNED_8BIT_OFFSET)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("value too large for 1-byte field"));
      *buf = value;
    }
}

static int
get_l16_shift (int reloc_type)
{
  switch (reloc_type)
    {
    case BFD_RELOC_C6000_SBR_L16_H:
      return 1;
    case BFD_RELOC_C6000_SBR_L16_W:
    case BFD_RELOC_C6000_SBR_GOT_L16_W:
      return 2;
    default:
      return 0;
    }
}

static void
handle_sbr_l16_relocs (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);
      int shift = get_l16_shift (fixP->fx_r_type);

      MODIFY_VALUE (newval, value, shift, 7, 16);
      if ((value + SIGNED_16BIT_OFFSET > SBR_U15_MAX + SIGNED_16BIT_OFFSET)
	  && (fixP->fx_r_type == BFD_RELOC_C6000_ABS_S16
	      || fixP->fx_r_type == BFD_RELOC_C6000_SBR_S16))
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("immediate offset out of range"));

      md_number_to_chars (buf, newval, 4);
    }
  if (fixP->fx_done
      && fixP->fx_r_type != BFD_RELOC_C6000_ABS_S16
      && fixP->fx_r_type != BFD_RELOC_C6000_ABS_L16)
    abort ();
}

static int
get_h16_shift (int reloc_type)
{
  switch (reloc_type)
    {
    case BFD_RELOC_C6000_SBR_H16_H:
      return 17;
    case BFD_RELOC_C6000_SBR_H16_W:
    case BFD_RELOC_C6000_SBR_GOT_H16_W:
      return 18;
    default:
      return 16;
    }
}

static void
handle_sbr_h16_relocs (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);
      int shift = get_h16_shift (fixP->fx_r_type);

      MODIFY_VALUE (newval, value, shift, 7, 16);
      md_number_to_chars (buf, newval, 4);
    }
  if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_ABS_H16)
    abort ();
}

static void
handle_pcr_16_relocs (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);
      int shift = fixP->fx_r_type == BFD_RELOC_C6000_PCR_H16 ? 16 : 0;

      MODIFY_VALUE (newval, value, shift, 7, 16);
      md_number_to_chars (buf, newval, 4);
    }
}

static void
handle_sbr_u15_b (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);

      MODIFY_VALUE (newval, value, 0, 8, 15);
      if (value > SBR_U15_MAX)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("immediate offset out of range"));

      md_number_to_chars (buf, newval, 4);
    }
}

static void
adjust_adda_value (fixS *fixP, valueT *value, int shift)
{
  if (fixP->tc_fix_data.fix_adda && fixP->fx_done)
    *value <<= shift;
}

static void
check_alignment (fixS *fixP, valueT value, int alignment, const char *msg)
{
  if (value & alignment)
    as_bad_where (fixP->fx_file, fixP->fx_line, _(msg));
}

static void
handle_sbr_u15_h (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);

      adjust_adda_value (fixP, &value, 1);
      MODIFY_VALUE (newval, value, 1, 8, 15);
      check_alignment (fixP, value, ALIGNMENT_2BYTE, "immediate offset not 2-byte-aligned");
      if (value > SBR_U15_H_MAX)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("immediate offset out of range"));

      md_number_to_chars (buf, newval, 4);
    }
}

static void
handle_sbr_u15_w (fixS *fixP, segT seg, char *buf, valueT value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);

      adjust_adda_value (fixP, &value, 2);
      MODIFY_VALUE (newval, value, 2, 8, 15);
      check_alignment (fixP, value, ALIGNMENT_4BYTE, "immediate offset not 4-byte-aligned");
      if (value > SBR_U15_W_MAX)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("immediate offset out of range"));

      md_number_to_chars (buf, newval, 4);
    }
  if (fixP->fx_done && fixP->fx_r_type != BFD_RELOC_C6000_SBR_U15_W)
    abort ();
}

static void
handle_dsbt_index (fixS *fixP, valueT value)
{
  if (value != 0)
    as_bad_where (fixP->fx_file, fixP->fx_line,
		  _("addend used with $DSBT_INDEX"));
  if (fixP->fx_done)
    abort ();
}

static void
handle_pcr_offset (fixS *fixP, segT seg, char *buf, valueT value,
		   int shift, int bit_pos, int bit_count,
		   valueT range, valueT max_value)
{
  if (fixP->fx_done || !seg->use_rela_p)
    {
      valueT newval = md_chars_to_number (buf, 4);

      MODIFY_VALUE (newval, value, shift, bit_pos, bit_count);
      check_alignment (fixP, value, ALIGNMENT_4BYTE, "PC-relative offset not 4-byte-aligned");
      if (value + range > max_value + range)
	as_bad_where (fixP->fx_file, fixP->fx_line,
		      _("PC-relative offset out of range"));

      md_number_to_chars (buf, newval, 4);
    }
}

static void
handle_pcr_s21 (fixS *fixP, segT seg, char *buf, valueT value)
{
  handle_pcr_offset (fixP, seg, buf, value, 2, 7, 21, PCR_S21_RANGE, PCR_S21_MAX);
}

static void
handle_pcr_s12 (fixS *fixP, segT seg, char *buf, valueT value)
{
  handle_pcr_offset (fixP, seg, buf, value, 2, 16, 12, PCR_S12_RANGE, PCR_S12_MAX);
}

static void
handle_pcr_s10 (fixS *fixP, segT seg, char *buf, valueT value)
{
  handle_pcr_offset (fixP, seg, buf, value, 2, 13, 10, PCR_S10_RANGE, PCR_S10_MAX);
}

static void
handle_pcr_s7 (fixS *fixP, segT seg, char *buf, valueT value)
{
  handle_pcr_offset (fixP, seg, buf, value, 2, 16, 7, PCR_S7_RANGE, PCR_S7_MAX);
}

/* Convert a floating-point number to target (IEEE) format.  */

const char *
md_atof (int type, char *litP, int *sizeP)
{
  return ieee_md_atof (type, litP, sizeP, target_big_endian);
}

/* Adjust the frags in SECTION (see tic6x_md_finish).  */

#define ALIGNMENT_8_BYTES 3
#define ALIGNMENT_16_BYTES 4
#define ALIGNMENT_32_BYTES 5
#define INSTRUCTION_SIZE 4
#define MAX_PACKET_INSNS 8
#define POS_MASK_32 31
#define POS_MASK_8 7
#define POS_MASK_16 15

typedef struct {
    frchainS *frchp;
    fragS *fragp;
    unsigned int pos;
} frag_position;

typedef struct {
    frag_position last32;
    frag_position last16;
    frag_position last8;
} alignment_positions;

typedef struct {
    unsigned int want_insert;
    unsigned int want_insert_done_so_far;
    unsigned int pos;
} nop_insertion_state;

static bool is_code_fragment(fragS *fragp)
{
    return fragp->fr_type == rs_machine_dependent && 
           fragp->tc_frag_data.is_insns;
}

static bool is_non_code_fragment(fragS *fragp)
{
    if (fragp->fr_type == rs_dummy || fragp->fr_type == rs_fill)
        return fragp->fr_fix > 0;
    return fragp->fr_type != rs_machine_dependent;
}

static void analyze_section_content(segment_info_type *info, bool *have_code, bool *have_non_code)
{
    frchainS *frchp;
    fragS *fragp;
    
    *have_code = false;
    *have_non_code = false;
    
    for (frchp = info->frchainP; frchp; frchp = frchp->frch_next)
        for (fragp = frchp->frch_root; fragp; fragp = fragp->fr_next)
        {
            if (is_code_fragment(fragp))
                *have_code = true;
            else if (is_non_code_fragment(fragp))
                *have_non_code = true;
        }
}

static void insert_nop_instruction(fragS *fragp, unsigned int offset)
{
    md_number_to_chars(fragp->fr_literal + fragp->fr_fix + offset, 0, INSTRUCTION_SIZE);
    if (target_big_endian)
        fragp->fr_literal[fragp->fr_fix + offset + INSTRUCTION_SIZE - 1] |= 0x1;
    else
        fragp->fr_literal[fragp->fr_fix + offset] |= 0x1;
}

static unsigned int get_current_want_nops(unsigned int want_insert)
{
    if (want_insert & 1)
        return 1;
    if (want_insert & 2)
        return 2;
    if (want_insert & 4)
        return 4;
    abort();
}

static void insert_nops_in_packet(fragS *fragp, nop_insertion_state *state)
{
    unsigned int num_insns = fragp->fr_fix >> 2;
    unsigned int max_poss_nops = MAX_PACKET_INSNS - num_insns;
    unsigned int cur_want_nops, max_want_nops, do_nops, i;
    
    if (!max_poss_nops)
        return;
    
    cur_want_nops = get_current_want_nops(state->want_insert);
    max_want_nops = cur_want_nops - state->want_insert_done_so_far;
    do_nops = (max_poss_nops < max_want_nops) ? max_poss_nops : max_want_nops;
    
    for (i = 0; i < do_nops; i++)
    {
        insert_nop_instruction(fragp, i * INSTRUCTION_SIZE);
        fragp->fr_fix += INSTRUCTION_SIZE;
        fragp->fr_var -= INSTRUCTION_SIZE;
    }
    
    state->want_insert_done_so_far += do_nops;
    if (state->want_insert_done_so_far == cur_want_nops)
    {
        state->want_insert -= state->want_insert_done_so_far;
        state->want_insert_done_so_far = 0;
    }
}

static void get_next_frag_position(frchainS **frchp, fragS **fragp)
{
    *fragp = (*fragp)->fr_next;
    if (*fragp == NULL)
    {
        *frchp = (*frchp)->frch_next;
        if (*frchp != NULL)
            *fragp = (*frchp)->frch_root;
    }
}

static void update_alignment_positions(alignment_positions *align_pos, 
                                      frchainS *frchp, fragS *fragp, unsigned int pos)
{
    frchainS *frchp_next = frchp;
    fragS *fragp_next = fragp;
    
    get_next_frag_position(&frchp_next, &fragp_next);
    
    if (!(pos & POS_MASK_8))
    {
        align_pos->last8.frchp = frchp_next;
        align_pos->last8.fragp = fragp_next;
        align_pos->last8.pos = pos;
    }
    if (!(pos & POS_MASK_16))
    {
        align_pos->last16.frchp = frchp_next;
        align_pos->last16.fragp = fragp_next;
        align_pos->last16.pos = pos;
    }
    if (!(pos & POS_MASK_32))
    {
        align_pos->last32.frchp = frchp_next;
        align_pos->last32.fragp = fragp_next;
        align_pos->last32.pos = pos;
    }
}

static void restore_position_for_backtrack(frchainS **frchp, fragS **fragp, 
                                          nop_insertion_state *state,
                                          alignment_positions *align_pos)
{
    if (state->want_insert & 1)
    {
        *frchp = align_pos->last8.frchp;
        *fragp = align_pos->last8.fragp;
        state->pos = align_pos->last8.pos;
    }
    else if (state->want_insert & 2)
    {
        *frchp = align_pos->last8.frchp = align_pos->last16.frchp;
        *fragp = align_pos->last8.fragp = align_pos->last16.fragp;
        state->pos = align_pos->last8.pos = align_pos->last16.pos;
    }
    else if (state->want_insert & 4)
    {
        *frchp = align_pos->last8.frchp = align_pos->last16.frchp = align_pos->last32.frchp;
        *fragp = align_pos->last8.fragp = align_pos->last16.fragp = align_pos->last32.fragp;
        state->pos = align_pos->last8.pos = align_pos->last16.pos = align_pos->last32.pos;
    }
    else
        abort();
}

static bool handle_boundary_crossing(fragS *fragp, nop_insertion_state *state)
{
    if (!fragp->tc_frag_data.is_insns || 
        state->pos + fragp->fr_fix <= 32 ||
        fragp->tc_frag_data.can_cross_fp_boundary)
        return false;
        
    if (state->want_insert)
        abort();
    if (state->pos & 3)
        abort();
        
    state->want_insert = (32 - state->pos) >> 2;
    if (state->want_insert > 7)
        abort();
    state->want_insert_done_so_far = 0;
    return true;
}

static bool handle_alignment_requirement(fragS *fragp, nop_insertion_state *state)
{
    unsigned int would_insert_bytes;
    
    if (fragp->tc_frag_data.is_insns)
        return false;
        
    if (!(state->pos & ((1 << fragp->fr_offset) - 1)))
        return false;
        
    if (state->want_insert)
        abort();
        
    would_insert_bytes = ((1 << fragp->fr_offset) - 
                         (state->pos & ((1 << fragp->fr_offset) - 1)));
                         
    if (fragp->fr_subtype != 0 && would_insert_bytes > fragp->fr_subtype)
        return false;
        
    if (fragp->fr_offset != ALIGNMENT_8_BYTES && 
        fragp->fr_offset != ALIGNMENT_16_BYTES && 
        fragp->fr_offset != ALIGNMENT_32_BYTES)
        abort();
        
    if (would_insert_bytes & 3)
        abort();
        
    state->want_insert = would_insert_bytes >> 2;
    if (state->want_insert > 7)
        abort();
    state->want_insert_done_so_far = 0;
    return true;
}

static void process_code_only_section(segment_info_type *info)
{
    nop_insertion_state state = {0, 0, 0};
    alignment_positions align_pos;
    frchainS *frchp;
    fragS *fragp;
    
    align_pos.last32.frchp = align_pos.last16.frchp = align_pos.last8.frchp = info->frchainP;
    align_pos.last32.fragp = align_pos.last16.fragp = align_pos.last8.fragp = info->frchainP->frch_root;
    align_pos.last32.pos = align_pos.last16.pos = align_pos.last8.pos = 0;
    
    for (frchp = info->frchainP; frchp; frchp = frchp->frch_next)
        for (fragp = frchp->frch_root; fragp; fragp = fragp->fr_next)
        {
look_at_frag:
            if (fragp->fr_type != rs_machine_dependent)
                continue;
                
            bool go_back = handle_boundary_crossing(fragp, &state);
            
            if (!go_back)
                go_back = handle_alignment_requirement(fragp, &state);
                
            if (!go_back && state.want_insert && fragp->tc_frag_data.is_insns)
            {
                insert_nops_in_packet(fragp, &state);
                if (state.want_insert)
                    go_back = true;
            }
            
            if (go_back)
            {
                restore_position_for_backtrack(&frchp, &fragp, &state, &align_pos);
                goto look_at_frag;
            }
            
            state.pos += fragp->fr_fix;
            state.pos &= POS_MASK_32;
            update_alignment_positions(&align_pos, frchp, fragp, state.pos);
        }
}

static void convert_machine_dependent_frags(segment_info_type *info)
{
    frchainS *frchp;
    fragS *fragp;
    
    for (frchp = info->frchainP; frchp; frchp = frchp->frch_next)
        for (fragp = frchp->frch_root; fragp; fragp = fragp->fr_next)
        {
            if (fragp->fr_type == rs_machine_dependent)
            {
                if (fragp->tc_frag_data.is_insns)
                    frag_wane(fragp);
                else
                {
                    fragp->fr_type = rs_align_code;
                    fragp->fr_var = 1;
                    *fragp->fr_literal = 0;
                }
            }
        }
}

static void tic6x_adjust_section(bfd *abfd ATTRIBUTE_UNUSED, segT section,
                                void *dummy ATTRIBUTE_UNUSED)
{
    segment_info_type *info;
    bool have_code;
    bool have_non_code;
    
    info = seg_info(section);
    if (info == NULL)
        return;
        
    analyze_section_content(info, &have_code, &have_non_code);
    
    if (have_code && !have_non_code)
        process_code_only_section(info);
        
    convert_machine_dependent_frags(info);
}

/* Initialize the machine-dependent parts of a frag.  */

void
tic6x_frag_init (fragS *fragp)
{
  fragp->tc_frag_data.is_insns = false;
  fragp->tc_frag_data.can_cross_fp_boundary = false;
}

/* Set an attribute if it has not already been set by the user.  */

static void
tic6x_set_attribute_int (int tag, int value)
{
  if (tag < 1 || tag >= NUM_KNOWN_OBJ_ATTRIBUTES)
    abort ();
    
  if (tic6x_attributes_set_explicitly[tag])
    return;
    
  if (!bfd_elf_add_proc_attr_int (stdoutput, tag, value))
    as_fatal (_("error adding attribute: %s"),
              bfd_errmsg (bfd_get_error ()));
}

/* Set object attributes deduced from the input file and command line
   rather than given explicitly.  */
static void
tic6x_set_attributes (void)
{
  if (tic6x_arch_attribute == C6XABI_Tag_ISA_none)
    tic6x_arch_attribute = C6XABI_Tag_ISA_C674X;

  tic6x_set_attribute_int (Tag_ISA, tic6x_arch_attribute);
  tic6x_set_attribute_int (Tag_ABI_DSBT, tic6x_dsbt);
  tic6x_set_attribute_int (Tag_ABI_PID, tic6x_pid);
  tic6x_set_attribute_int (Tag_ABI_PIC, tic6x_pic);
}

/* Do machine-dependent manipulations of the frag chains after all
   input has been read and before the machine-independent sizing and
   relaxing.  */

void tic6x_md_finish(void)
{
    tic6x_set_attributes();
    bfd_map_over_sections(stdoutput, tic6x_adjust_section, NULL);
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED, segT asec ATTRIBUTE_UNUSED,
		 fragS *fragp ATTRIBUTE_UNUSED)
{
  abort ();
}

/* No machine-dependent frags at this stage; all converted in
   tic6x_md_finish.  */

int
md_estimate_size_before_relax (fragS *fragp ATTRIBUTE_UNUSED,
                               segT seg ATTRIBUTE_UNUSED)
{
  abort ();
}

/* Put a number into target byte order.  */

void md_number_to_chars(char *buf, valueT val, int n)
{
  void (*number_to_chars_func)(char *, valueT, int) = 
    target_big_endian ? number_to_chars_bigendian : number_to_chars_littleendian;
  
  number_to_chars_func(buf, val, n);
}

/* Machine-dependent operand parsing not currently needed.  */

void
md_operand (expressionS *op ATTRIBUTE_UNUSED)
{
}

/* PC-relative operands are relative to the start of the fetch
   packet.  */

long
tic6x_pcrel_from_section (fixS *fixp, segT sec)
{
  const unsigned long long ALIGNMENT_MASK = 0x1fULL;
  
  if (fixp->fx_addsy != NULL
      && (!S_IS_DEFINED (fixp->fx_addsy)
	  || S_GET_SEGMENT (fixp->fx_addsy) != sec))
    return 0;
  return (fixp->fx_where + fixp->fx_frag->fr_address) & ~ALIGNMENT_MASK;
}

/* Round up a section size to the appropriate boundary.  */

valueT
md_section_align (segT segment ATTRIBUTE_UNUSED,
		  valueT size)
{
  int align = bfd_section_alignment (segment);
  valueT alignment_mask = (valueT) 1 << align;
  valueT alignment_offset = alignment_mask - 1;
  return (size + alignment_offset) & ~alignment_offset;
}

/* No special undefined symbol handling needed for now.  */

symbolS *
md_undefined_symbol (char *name ATTRIBUTE_UNUSED)
{
  return NULL;
}

/* Translate internal representation of relocation info to BFD target
   format.  */

arelent *
tc_gen_reloc (asection *section ATTRIBUTE_UNUSED, fixS *fixp)
{
  arelent *reloc = create_relocation(fixp);
  if (!reloc)
    return NULL;

  if (!validate_relocation(reloc, fixp))
    return NULL;

  adjust_relocation_addend(reloc, fixp);
  handle_pcr_relocation(reloc, fixp);

  return reloc;
}

static arelent *
create_relocation(fixS *fixp)
{
  arelent *reloc = notes_alloc(sizeof(arelent));
  reloc->sym_ptr_ptr = notes_alloc(sizeof(asymbol *));
  *reloc->sym_ptr_ptr = symbol_get_bfdsym(fixp->fx_addsy);
  reloc->address = fixp->fx_frag->fr_address + fixp->fx_where;
  reloc->addend = tic6x_generate_rela ? fixp->fx_offset : 0;
  reloc->howto = bfd_reloc_type_lookup(stdoutput, fixp->fx_r_type);
  return reloc;
}

static bool
validate_relocation(arelent *reloc, fixS *fixp)
{
  if (reloc->howto != NULL)
    return true;

  as_bad_where(fixp->fx_file, fixp->fx_line,
               _("Cannot represent relocation type %s"),
               bfd_get_reloc_code_name(fixp->fx_r_type));
  return false;
}

static void
adjust_relocation_addend(arelent *reloc, fixS *fixp)
{
  if (!reloc->howto->pcrel_offset || !reloc->howto->partial_inplace)
    return;

  reloc->addend += reloc->address;
  asymbol *symbol = *reloc->sym_ptr_ptr;
  if (!bfd_is_com_section(bfd_asymbol_section(symbol)))
    reloc->addend -= symbol->value;
}

static void
handle_pcr_relocation(arelent *reloc, fixS *fixp)
{
  bfd_reloc_code_real_type r_type = fixp->fx_r_type;
  if (r_type != BFD_RELOC_C6000_PCR_H16 && r_type != BFD_RELOC_C6000_PCR_L16)
    return;

  symbolS *sub_symbol = fixp->tc_fix_data.fix_subsy;
  resolve_symbol_value(sub_symbol);
  
  if (S_GET_SEGMENT(sub_symbol) == undefined_section)
    {
      as_bad_where(fixp->fx_file, fixp->fx_line,
                   _("undefined symbol %s in PCR relocation"),
                   S_GET_NAME(sub_symbol));
    }
  else
    {
      #define PCR_ADDRESS_MASK 0x1F
      reloc->addend = reloc->address & ~PCR_ADDRESS_MASK;
      reloc->addend -= S_GET_VALUE(sub_symbol);
    }
}

/* Convert REGNAME to a DWARF-2 register number.  */

int
tic6x_regname_to_dw2regnum (char *regname)
{
  bool reg_ok;
  tic6x_register reg;
  char *rq = regname;

  reg_ok = tic6x_parse_register (&rq, &reg);

  if (!reg_ok)
    return -1;

  return tic6x_calculate_dw2regnum(&reg);
}

static int
tic6x_calculate_dw2regnum(tic6x_register *reg)
{
  #define A_SIDE 1
  #define B_SIDE 2
  #define STANDARD_REG_LIMIT 16
  #define EXTENDED_REG_LIMIT 32
  #define A_EXTENDED_OFFSET 37
  #define B_STANDARD_OFFSET 16
  #define B_EXTENDED_OFFSET 53

  if (reg->side == A_SIDE)
    return tic6x_map_a_side_register(reg->num);
  
  if (reg->side == B_SIDE)
    return tic6x_map_b_side_register(reg->num);
  
  return -1;
}

static int
tic6x_map_a_side_register(int num)
{
  if (num < STANDARD_REG_LIMIT)
    return num;
  
  if (num < EXTENDED_REG_LIMIT)
    return (num - STANDARD_REG_LIMIT) + A_EXTENDED_OFFSET;
  
  return -1;
}

static int
tic6x_map_b_side_register(int num)
{
  if (num < STANDARD_REG_LIMIT)
    return num + B_STANDARD_OFFSET;
  
  if (num < EXTENDED_REG_LIMIT)
    return (num - STANDARD_REG_LIMIT) + B_EXTENDED_OFFSET;
  
  return -1;
}

/* Initialize the DWARF-2 unwind information for this procedure.  */

void
tic6x_frame_initial_instructions (void)
{
  const int STACK_POINTER_REG = 31;
  const int INITIAL_OFFSET = 0;
  
  cfi_add_CFA_def_cfa (STACK_POINTER_REG, INITIAL_OFFSET);
}

/* Start an exception table entry.  If idx is nonzero this is an index table
   entry.  */

static void get_unwind_prefix_and_type(int idx, const char **prefix, const char **prefix_once, int *type)
{
  if (idx)
    {
      *prefix = ELF_STRING_C6000_unwind;
      *prefix_once = ELF_STRING_C6000_unwind_once;
      *type = SHT_C6000_UNWIND;
    }
  else
    {
      *prefix = ELF_STRING_C6000_unwind_info;
      *prefix_once = ELF_STRING_C6000_unwind_info_once;
      *type = SHT_PROGBITS;
    }
}

static const char* get_processed_text_name(const segT text_seg)
{
  const char *text_name = segment_name (text_seg);
  if (streq (text_name, ".text"))
    return "";
  return text_name;
}

static const char* adjust_prefix_for_linkonce(const char **text_name, const char *prefix, const char *prefix_once)
{
  const char *LINKONCE_PREFIX = ".gnu.linkonce.t.";
  
  if (startswith (*text_name, LINKONCE_PREFIX))
    {
      *text_name += strlen (LINKONCE_PREFIX);
      return prefix_once;
    }
  return prefix;
}

static char* build_section_name(const char *prefix, const char *text_name)
{
  size_t prefix_len = strlen (prefix);
  size_t text_len = strlen (text_name);
  size_t sec_name_len = prefix_len + text_len;
  char *sec_name = XNEWVEC (char, sec_name_len + 1);
  
  memcpy (sec_name, prefix, prefix_len);
  memcpy (sec_name + prefix_len, text_name, text_len);
  sec_name[sec_name_len] = '\0';
  
  return sec_name;
}

static int handle_comdat_group(const segT text_seg, const char *prefix, const char *prefix_once, 
                                struct elf_section_match *match, int *linkonce)
{
  int flags = SHF_ALLOC;
  *linkonce = 0;
  
  if (prefix == prefix_once || (text_seg->flags & SEC_LINK_ONCE) == 0)
    return flags;
    
  match->group_name = elf_group_name (text_seg);
  if (match->group_name == NULL)
    {
      as_bad (_("group section `%s' has no group signature"),
              segment_name (text_seg));
      ignore_rest_of_line ();
      return -1;
    }
  flags |= SHF_GROUP;
  *linkonce = 1;
  
  return flags;
}

static void
tic6x_start_unwind_section (const segT text_seg, int idx)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();
  const char *prefix;
  const char *prefix_once;
  const char *text_name;
  struct elf_section_match match;
  char *sec_name;
  int type;
  int flags;
  int linkonce;

  get_unwind_prefix_and_type(idx, &prefix, &prefix_once, &type);
  
  text_name = get_processed_text_name(text_seg);
  prefix = adjust_prefix_for_linkonce(&text_name, prefix, prefix_once);
  
  sec_name = build_section_name(prefix, text_name);

  memset (&match, 0, sizeof (match));
  flags = handle_comdat_group(text_seg, prefix, prefix_once, &match, &linkonce);
  
  if (flags == -1)
    return;

  obj_elf_change_section (sec_name, type, flags, 0, &match, linkonce);

  if (idx)
    elf_linked_to_section (now_seg) = text_seg;

  seg_info (now_seg)->tc_segment_info_data.text_unwind = unwind;
}


static const int
tic6x_unwind_frame_regs[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { 15, 31, 30, 29, 28, 27, 26, 19, 14, 13, 12, 11, 10 };

/* Register save offsets for __c6xabi_push_rts.  */
static const int
tic6x_pop_rts_offset_little[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { -1,  1,  0, -3, -4, -7, -8,-11, -2, -5, -6, -9,-10};

static const int
tic6x_pop_rts_offset_big[TIC6X_NUM_UNWIND_REGS] =
/* A15 B15 B14 B13 B12 B11 B10  B3 A14 A13 A12 A11 A10.  */
  { -2,  1,  0, -4, -3, -8, -7,-12, -1, -6, -5,-10, -9};

/* Map from dwarf register number to unwind frame register number.  */
static int
tic6x_unwind_reg_from_dwarf (int dwarf)
{
  int reg;

  for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
      if (tic6x_unwind_frame_regs[reg] == dwarf)
	return reg;
    }

  return -1;
}

/* Unwinding bytecode definitions.  */
#define UNWIND_OP_ADD_SP  0x00
#define UNWIND_OP_ADD_SP2 0xd2
#define UNWIND_OP2_POP 0x8000
#define UNWIND_OP2_POP_COMPACT 0xa000
#define UNWIND_OP_POP_REG 0xc0
#define UNWIND_OP_MV_FP 0xd0
#define UNWIND_OP_POP_RTS 0xd1
#define UNWIND_OP_RET 0xe0

/* Maximum stack adjustment for __c6xabi_unwind_cpp_pr3/4 */
#define MAX_COMPACT_SP_OFFSET (0x7f << 3)

static void create_extab_entry_if_needed(tic6x_unwind_info *unwind)
{
    if (unwind->table_entry != NULL)
        return;
        
    tic6x_start_unwind_section(unwind->saved_seg, 0);
    frag_align(2, 0, 0);
    record_alignment(now_seg, 2);
    unwind->table_entry = expr_build_dot();
}

static void tic6x_flush_unwind_word(valueT data)
{
    tic6x_unwind_info *unwind = tic6x_get_unwind();
    char *ptr;
    
    create_extab_entry_if_needed(unwind);
    
    ptr = frag_more(4);
    
    if (unwind->table_entry != NULL && unwind->frag_start == NULL)
        unwind->frag_start = ptr;
        
    md_number_to_chars(ptr, data, 4);
}

/* Add a single byte of unwinding data.  */

static void flush_first_word_for_pr1(tic6x_unwind_info *unwind, int byte)
{
    unwind->personality_index = 1;
    tic6x_flush_unwind_word (0x81000000 | ((unwind->data >> 8) & 0xffff));
    unwind->data = ((unwind->data & 0xff) << 8) | byte;
    unwind->data_bytes++;
}

static void flush_regular_word(tic6x_unwind_info *unwind, int byte)
{
    tic6x_flush_unwind_word (unwind->data);
    unwind->data = byte;
}

static void append_byte_to_data(tic6x_unwind_info *unwind, int byte)
{
    unwind->data = (unwind->data << 8) | byte;
}

static int should_flush_word(tic6x_unwind_info *unwind)
{
    return (unwind->data_bytes & 3) == 0 && unwind->data_bytes > 4;
}

static void handle_fifth_byte(tic6x_unwind_info *unwind, int byte)
{
    if (unwind->personality_index == -1)
        flush_first_word_for_pr1(unwind, byte);
    else
        flush_regular_word(unwind, byte);
}

static void handle_other_bytes(tic6x_unwind_info *unwind, int byte)
{
    append_byte_to_data(unwind, byte);
    if (should_flush_word(unwind))
    {
        tic6x_flush_unwind_word (unwind->data);
        unwind->data = 0;
    }
}

static void
tic6x_unwind_byte (int byte)
{
    tic6x_unwind_info *unwind = tic6x_get_unwind ();

    unwind->data_bytes++;
    
    if (unwind->data_bytes == 5)
        handle_fifth_byte(unwind, byte);
    else
        handle_other_bytes(unwind, byte);
}

/* Add a two-byte unwinding opcode.  */
static void
tic6x_unwind_2byte (int bytes)
{
  #define HIGH_BYTE_SHIFT 8
  #define LOW_BYTE_MASK 0xff
  
  tic6x_unwind_byte (bytes >> HIGH_BYTE_SHIFT);
  tic6x_unwind_byte (bytes & LOW_BYTE_MASK);
}

static void
tic6x_unwind_uleb (offsetT offset)
{
  const unsigned char ULEB_CONTINUATION_BIT = 0x80;
  const unsigned char ULEB_VALUE_MASK = 0x7f;
  const int ULEB_SHIFT_BITS = 7;

  while (offset > ULEB_VALUE_MASK)
    {
      tic6x_unwind_byte ((offset & ULEB_VALUE_MASK) | ULEB_CONTINUATION_BIT);
      offset >>= ULEB_SHIFT_BITS;
    }
  tic6x_unwind_byte (offset);
}

void
tic6x_cfi_startproc (void)
{
  tic6x_unwind_info *unwind = tic6x_get_unwind ();

  unwind->personality_index = -1;
  unwind->personality_routine = NULL;
  
  if (unwind->table_entry)
    as_bad (_("missing .endp before .cfi_startproc"));

  unwind->table_entry = NULL;
  unwind->data_bytes = -1;
}

static void create_index_table_entry(tic6x_unwind_info *unwind, long *where)
{
    char *ptr;
    
    frag_align(2, 0, 0);
    record_alignment(now_seg, 2);
    
    ptr = frag_more(8);
    memset(ptr, 0, 8);
    *where = frag_now_fix() - 8;
    
    fix_new(frag_now, *where, 4, unwind->function_start, 0, 1,
            BFD_RELOC_C6000_PREL31);
    
    if (unwind->table_entry) {
        fix_new(frag_now, *where + 4, 4, unwind->table_entry, 0, 1,
                BFD_RELOC_C6000_PREL31);
    } else {
        md_number_to_chars(ptr + 4, unwind->data, 4);
    }
}

static const char* get_personality_routine_name(int index)
{
    static const char *const name[] = {
        "__c6xabi_unwind_cpp_pr0",
        "__c6xabi_unwind_cpp_pr1",
        "__c6xabi_unwind_cpp_pr2",
        "__c6xabi_unwind_cpp_pr3",
        "__c6xabi_unwind_cpp_pr4"
    };
    return name[index];
}

static int is_personality_index_valid(int index)
{
    return index >= 0 && index < 5;
}

static int is_dependency_marked(unsigned int marked_pr_dependency, int index)
{
    return marked_pr_dependency & (1 << index);
}

static void mark_personality_dependency(tic6x_unwind_info *unwind, long where)
{
    unsigned int marked_pr_dependency;
    symbolS *pr;
    
    marked_pr_dependency = seg_info(now_seg)->tc_segment_info_data.marked_pr_dependency;
    
    if (!is_personality_index_valid(unwind->personality_index))
        return;
    
    if (is_dependency_marked(marked_pr_dependency, unwind->personality_index))
        return;
    
    pr = symbol_find_or_make(get_personality_routine_name(unwind->personality_index));
    fix_new(frag_now, where, 0, pr, 0, 1, BFD_RELOC_NONE);
    seg_info(now_seg)->tc_segment_info_data.marked_pr_dependency |= 1 << unwind->personality_index;
}

static void tic6x_output_exidx_entry(void)
{
    long where;
    segT old_seg;
    subsegT old_subseg;
    tic6x_unwind_info *unwind = tic6x_get_unwind();
    
    old_seg = now_seg;
    old_subseg = now_subseg;
    
    tic6x_start_unwind_section(unwind->saved_seg, 1);
    create_index_table_entry(unwind, &where);
    mark_personality_dependency(unwind, where);
    
    subseg_set(old_seg, old_subseg);
}

#define UNWIND_DATA_PERSONALITY_MASK (1u << 31)
#define UNWIND_DATA_PERSONALITY_SHIFT 24
#define UNWIND_CFA_REG_FP 15
#define UNWIND_CFA_FP_OFFSET 0x7f
#define UNWIND_CFA_OFFSET_SHIFT 17
#define UNWIND_CFA_OFFSET_ADJ 3
#define UNWIND_SAFE_MASK_SHIFT 4
#define UNWIND_COMPACT_MASK_SHIFT 4
#define UNWIND_PERSONALITY_WORD_SIZE 4
#define UNWIND_PERSONALITY_ROUTINE_SIZE 5
#define UNWIND_PERSONALITY_INDEX_MASK 0x8000
#define UNWIND_PERSONALITY_INDEX_SHIFT 8
#define UNWIND_PERSONALITY_PR0_MASK 0x80
#define UNWIND_PERSONALITY_INDEX_2_SIZE 2
#define UNWIND_PERSONALITY_INDEX_1_SIZE 1
#define UNWIND_CFA_LARGE_OFFSET 0x80
#define UNWIND_CFA_MEDIUM_OFFSET 0x40
#define UNWIND_CFA_LARGE_ADJUST 0x81
#define UNWIND_CFA_MEDIUM_ADJUST 0x40
#define UNWIND_CFA_SHIFT 3
#define UNWIND_OP_ADD_SP_MAX 0x3f
#define UNWIND_REG_NIBBLE_SIZE 4
#define UNWIND_REG_NIBBLE_SHIFT 4
#define UNWIND_REG_INVALID 0xf
#define UNWIND_DATA_ALIGN 3
#define UNWIND_EXTAB_EMPTY 4
#define UNWIND_MAX_BYTECODE 0x400
#define UNWIND_PR1_DATA_OFFSET 8
#define UNWIND_PR1_DATA_SHIFT 2
#define UNWIND_PR1_LENGTH_SHIFT 24
#define UNWIND_PR2_DATA_OFFSET 4
#define UNWIND_PR2_DATA_SHIFT 2
#define UNWIND_PR2_LENGTH_SHIFT 16
#define PERSONALITY_PR3 3
#define PERSONALITY_PR4 4
#define PERSONALITY_UNDECIDED -1
#define PERSONALITY_CANNOT_UNWIND -2

static void handle_cannot_unwind(tic6x_unwind_info *unwind)
{
    unwind->data = 1;
    tic6x_output_exidx_entry();
}

static void auto_select_personality(tic6x_unwind_info *unwind)
{
    if (unwind->reg_saved_mask || unwind->cfa_offset >= MAX_COMPACT_SP_OFFSET)
        unwind->personality_index = PERSONALITY_UNDECIDED;
    else if (unwind->safe_mask)
        unwind->personality_index = PERSONALITY_PR3;
    else
        unwind->personality_index = PERSONALITY_PR4;
}

static bool validate_compact_personality(tic6x_unwind_info *unwind)
{
    if (unwind->cfa_offset >= MAX_COMPACT_SP_OFFSET)
    {
        as_bad(_("stack pointer offset too large for personality routine"));
        return false;
    }
    
    if (unwind->reg_saved_mask ||
        (unwind->personality_index == PERSONALITY_PR3 && unwind->compact_mask != 0) ||
        (unwind->personality_index == PERSONALITY_PR4 && unwind->safe_mask != 0))
    {
        as_bad(_("stack frame layout does not match personality routine"));
        return false;
    }
    
    return true;
}

static void build_compact_personality_data(tic6x_unwind_info *unwind)
{
    unwind->data = UNWIND_DATA_PERSONALITY_MASK | 
                   (unwind->personality_index << UNWIND_DATA_PERSONALITY_SHIFT);
    
    if (unwind->cfa_reg == UNWIND_CFA_REG_FP)
        unwind->data |= UNWIND_CFA_FP_OFFSET << UNWIND_CFA_OFFSET_SHIFT;
    else
        unwind->data |= unwind->cfa_offset << (UNWIND_CFA_OFFSET_SHIFT - UNWIND_CFA_OFFSET_ADJ);
    
    if (unwind->personality_index == PERSONALITY_PR3)
        unwind->data |= unwind->safe_mask << UNWIND_SAFE_MASK_SHIFT;
    else
        unwind->data |= unwind->compact_mask << UNWIND_COMPACT_MASK_SHIFT;
    
    unwind->data |= unwind->return_reg;
    unwind->data_bytes = UNWIND_PERSONALITY_WORD_SIZE;
}

static void emit_personality_routine(tic6x_unwind_info *unwind)
{
    long where;
    
    unwind->data = 0;
    unwind->data_bytes = UNWIND_PERSONALITY_ROUTINE_SIZE;
    tic6x_flush_unwind_word(0);
    where = frag_now_fix() - 4;
    fix_new(frag_now, where, 4, unwind->personality_routine, 0, 1, BFD_RELOC_C6000_PREL31);
}

static void setup_personality_data(tic6x_unwind_info *unwind)
{
    if (unwind->personality_routine)
    {
        emit_personality_routine(unwind);
    }
    else if (unwind->personality_index > 0)
    {
        unwind->data = UNWIND_PERSONALITY_INDEX_MASK | 
                       (unwind->personality_index << UNWIND_PERSONALITY_INDEX_SHIFT);
        unwind->data_bytes = UNWIND_PERSONALITY_INDEX_2_SIZE;
    }
    else
    {
        unwind->data = UNWIND_PERSONALITY_PR0_MASK;
        unwind->data_bytes = UNWIND_PERSONALITY_INDEX_1_SIZE;
    }
}

static void emit_return_register(tic6x_unwind_info *unwind)
{
    if (unwind->return_reg != UNWIND_B3)
        tic6x_unwind_byte(UNWIND_OP_RET | unwind->return_reg);
}

static void emit_cfa_adjustment(tic6x_unwind_info *unwind)
{
    offsetT cfa_offset = unwind->cfa_offset;
    
    if (unwind->cfa_reg == UNWIND_CFA_REG_FP)
    {
        tic6x_unwind_byte(UNWIND_OP_MV_FP);
    }
    else if (cfa_offset != 0)
    {
        cfa_offset >>= UNWIND_CFA_SHIFT;
        if (cfa_offset > UNWIND_CFA_LARGE_OFFSET)
        {
            tic6x_unwind_byte(UNWIND_OP_ADD_SP2);
            tic6x_unwind_uleb(cfa_offset - UNWIND_CFA_LARGE_ADJUST);
        }
        else if (cfa_offset > UNWIND_CFA_MEDIUM_OFFSET)
        {
            tic6x_unwind_byte(UNWIND_OP_ADD_SP | UNWIND_OP_ADD_SP_MAX);
            tic6x_unwind_byte(UNWIND_OP_ADD_SP | (cfa_offset - UNWIND_CFA_MEDIUM_ADJUST));
        }
        else
        {
            tic6x_unwind_byte(UNWIND_OP_ADD_SP | (cfa_offset - 1));
        }
    }
}

static void emit_pop_operations(tic6x_unwind_info *unwind)
{
    if (unwind->safe_mask)
        tic6x_unwind_2byte(UNWIND_OP2_POP | unwind->safe_mask);
    else if (unwind->pop_rts)
        tic6x_unwind_byte(UNWIND_OP_POP_RTS);
    else if (unwind->compact_mask)
        tic6x_unwind_2byte(UNWIND_OP2_POP_COMPACT | unwind->compact_mask);
}

static void emit_saved_registers(tic6x_unwind_info *unwind)
{
    offsetT cur_offset;
    int val, last_val = 0;
    int reg;
    
    tic6x_unwind_byte(UNWIND_OP_POP_REG | unwind->saved_reg_count);
    
    for (cur_offset = 0; unwind->saved_reg_count > 0; cur_offset -= 4)
    {
        val = UNWIND_REG_INVALID;
        for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
        {
            if (!unwind->reg_saved[reg])
                continue;
            
            if (unwind->reg_offset[reg] == cur_offset)
            {
                unwind->saved_reg_count--;
                val = reg;
                break;
            }
        }
        
        if ((cur_offset & UNWIND_REG_NIBBLE_SIZE) == UNWIND_REG_NIBBLE_SIZE)
            tic6x_unwind_byte((last_val << UNWIND_REG_NIBBLE_SHIFT) | val);
        else
            last_val = val;
    }
    
    if ((cur_offset & UNWIND_REG_NIBBLE_SIZE) == UNWIND_REG_NIBBLE_SIZE)
        tic6x_unwind_byte((last_val << UNWIND_REG_NIBBLE_SHIFT) | UNWIND_REG_INVALID);
}

static void pad_unwind_data(tic6x_unwind_info *unwind)
{
    while ((unwind->data_bytes & UNWIND_DATA_ALIGN) != 0)
        tic6x_unwind_byte(UNWIND_OP_RET | UNWIND_B3);
}

static void emit_generic_personality(tic6x_unwind_info *unwind)
{
    setup_personality_data(unwind);
    emit_return_register(unwind);
    emit_cfa_adjustment(unwind);
    emit_pop_operations(unwind);
    
    if (unwind->reg_saved_mask)
        emit_saved_registers(unwind);
    
    pad_unwind_data(unwind);
    
    if (unwind->personality_index == PERSONALITY_UNDECIDED && 
        unwind->personality_routine == NULL)
        unwind->personality_index = 0;
}

static void force_extab_entry(tic6x_unwind_info *unwind, bool need_extab)
{
    if (need_extab && !unwind->table_entry)
    {
        if (unwind->data_bytes != UNWIND_EXTAB_EMPTY)
            abort();
        tic6x_flush_unwind_word(unwind->data);
    }
    else if (unwind->table_entry && !need_extab)
    {
        char *ptr = frag_more(4);
        md_number_to_chars(ptr, 0, 4);
    }
}

static void update_unwinding_length(tic6x_unwind_info *unwind)
{
    valueT tmp;
    
    if (!unwind->table_entry)
        return;
    
    if (unwind->data_bytes > UNWIND_MAX_BYTECODE)
        as_bad(_("too many unwinding instructions"));
    
    if (unwind->personality_index == PERSONALITY_UNDECIDED)
    {
        tmp = md_chars_to_number(unwind->frag_start + 4, 4);
        tmp |= (valueT)((unwind->data_bytes - UNWIND_PR1_DATA_OFFSET) >> 
                        UNWIND_PR1_DATA_SHIFT) << UNWIND_PR1_LENGTH_SHIFT;
        md_number_to_chars(unwind->frag_start + 4, tmp, 4);
    }
    else if (unwind->personality_index == 1 || unwind->personality_index == 2)
    {
        tmp = md_chars_to_number(unwind->frag_start, 4);
        tmp |= ((unwind->data_bytes - UNWIND_PR2_DATA_OFFSET) >> 
                UNWIND_PR2_DATA_SHIFT) << UNWIND_PR2_LENGTH_SHIFT;
        md_number_to_chars(unwind->frag_start, tmp, 4);
    }
}

static void tic6x_output_unwinding(bool need_extab)
{
    tic6x_unwind_info *unwind = tic6x_get_unwind();
    
    if (unwind->personality_index == PERSONALITY_CANNOT_UNWIND)
    {
        handle_cannot_unwind(unwind);
        return;
    }
    
    if (unwind->personality_index == PERSONALITY_UNDECIDED && 
        unwind->personality_routine == NULL)
    {
        auto_select_personality(unwind);
    }
    
    unwind->table_entry = NULL;
    
    if (unwind->personality_index == PERSONALITY_PR3 || 
        unwind->personality_index == PERSONALITY_PR4)
    {
        if (!validate_compact_personality(unwind))
            return;
        build_compact_personality_data(unwind);
    }
    else
    {
        emit_generic_personality(unwind);
    }
    
    force_extab_entry(unwind, need_extab);
    update_unwinding_length(unwind);
    tic6x_output_exidx_entry();
}

/* FIXME: This will get horribly confused if cfi directives are emitted for
   function epilogue.  */
#define UNWIND_B15 15
#define UNWIND_B3 3
#define TIC6X_NUM_UNWIND_REGS 32
#define ALIGNMENT_MASK 7
#define DOUBLEWORD_ALIGNMENT 8
#define WORD_SIZE 4
#define MAX_SAVE_OFFSET 0x800
#define POP_RTS_MASK 0x17ff
#define CFA_REG_SP 31
#define CFA_REG_FP 15
#define RETURN_ADDRESS_REG 19

static bool is_valid_unwind_reg(int reg)
{
    return reg >= 0 && reg < TIC6X_NUM_UNWIND_REGS;
}

static void report_unwind_error(const char *format, int reg)
{
    as_bad(format, reg);
}

static void initialize_unwind_info(tic6x_unwind_info *unwind)
{
    int reg;
    
    unwind->cfa_reg = CFA_REG_SP;
    unwind->return_reg = UNWIND_B3;
    unwind->saved_reg_count = 0;
    unwind->pop_rts = false;
    unwind->saved_seg = now_seg;
    unwind->saved_subseg = now_subseg;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
        unwind->reg_saved[reg] = false;
}

static void process_undefined_or_same_value(tic6x_unwind_info *unwind, int dwarf_reg)
{
    int reg = tic6x_unwind_reg_from_dwarf(dwarf_reg);
    if (is_valid_unwind_reg(reg))
        unwind->reg_saved[reg] = false;
}

static bool process_offset_insn(tic6x_unwind_info *unwind, struct cfi_insn_data *insn)
{
    int reg = tic6x_unwind_reg_from_dwarf(insn->u.ri.reg);
    
    if (!is_valid_unwind_reg(reg))
    {
        report_unwind_error(_("unable to generate unwinding opcode for reg %d"), 
                           insn->u.ri.reg);
        return false;
    }
    
    unwind->reg_saved[reg] = true;
    unwind->reg_offset[reg] = insn->u.ri.offset;
    
    if (insn->u.ri.reg == UNWIND_B3)
        unwind->return_reg = UNWIND_B3;
    
    return true;
}

static bool process_register_insn(tic6x_unwind_info *unwind, struct cfi_insn_data *insn)
{
    int reg;
    
    if (insn->u.rr.reg1 != RETURN_ADDRESS_REG)
    {
        report_unwind_error(_("unable to generate unwinding opcode for reg %d"), 
                           insn->u.rr.reg1);
        return false;
    }
    
    reg = tic6x_unwind_reg_from_dwarf(insn->u.rr.reg2);
    if (!is_valid_unwind_reg(reg))
    {
        report_unwind_error(_("unable to generate unwinding opcode for reg %d"), 
                           insn->u.rr.reg2);
        return false;
    }
    
    unwind->return_reg = reg;
    unwind->reg_saved[UNWIND_B3] = false;
    
    if (unwind->reg_saved[reg])
    {
        as_bad(_("unable to restore return address from previously restored reg"));
        return false;
    }
    
    return true;
}

static bool process_cfi_instruction(tic6x_unwind_info *unwind, 
                                   struct cfi_insn_data *insn, 
                                   offsetT *cfa_offset)
{
    switch (insn->insn)
    {
    case DW_CFA_advance_loc:
        break;
        
    case DW_CFA_def_cfa:
        unwind->cfa_reg = insn->u.ri.reg;
        *cfa_offset = insn->u.ri.offset;
        break;
        
    case DW_CFA_def_cfa_register:
        unwind->cfa_reg = insn->u.r;
        break;
        
    case DW_CFA_def_cfa_offset:
        *cfa_offset = insn->u.i;
        break;
        
    case DW_CFA_undefined:
    case DW_CFA_same_value:
        process_undefined_or_same_value(unwind, insn->u.r);
        break;
        
    case DW_CFA_offset:
        if (!process_offset_insn(unwind, insn))
            return false;
        break;
        
    case DW_CFA_register:
        if (!process_register_insn(unwind, insn))
            return false;
        break;
        
    case DW_CFA_restore:
    case DW_CFA_remember_state:
    case DW_CFA_restore_state:
    case DW_CFA_GNU_window_save:
    case CFI_escape:
    case CFI_val_encoded_addr:
        as_bad(_("unhandled CFA insn for unwinding (%d)"), insn->insn);
        break;
        
    default:
        abort();
    }
    
    return true;
}

static bool validate_cfa_settings(tic6x_unwind_info *unwind, offsetT cfa_offset)
{
    if (unwind->cfa_reg != CFA_REG_FP && unwind->cfa_reg != CFA_REG_SP)
    {
        report_unwind_error(_("unable to generate unwinding opcode for frame pointer reg %d"),
                           unwind->cfa_reg);
        return false;
    }
    
    if (unwind->cfa_reg == CFA_REG_FP)
    {
        if (cfa_offset != 0)
        {
            as_bad(_("unable to generate unwinding opcode for frame pointer offset"));
            return false;
        }
    }
    else
    {
        if ((cfa_offset & ALIGNMENT_MASK) != 0)
        {
            as_bad(_("unwound stack pointer not doubleword aligned"));
            return false;
        }
    }
    
    return true;
}

static unsigned compute_reg_saved_mask(tic6x_unwind_info *unwind)
{
    unsigned mask = 0;
    int reg;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
        if (unwind->reg_saved[reg])
            mask |= 1 << (TIC6X_NUM_UNWIND_REGS - (reg + 1));
    }
    
    return mask;
}

static bool is_swapped_pair(tic6x_unwind_info *unwind, int reg, offsetT save_offset)
{
    return target_big_endian
        && reg < TIC6X_NUM_UNWIND_REGS - 1
        && unwind->reg_saved[reg + 1]
        && tic6x_unwind_frame_regs[reg] == tic6x_unwind_frame_regs[reg + 1] + 1
        && (tic6x_unwind_frame_regs[reg] & 1) == 1
        && (save_offset & WORD_SIZE) == WORD_SIZE;
}

static unsigned check_safe_debug_layout(tic6x_unwind_info *unwind, unsigned reg_saved_mask)
{
    offsetT save_offset = 0;
    int reg;
    
    if (!reg_saved_mask)
        return 0;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
        if (!unwind->reg_saved[reg])
            continue;
        
        if (is_swapped_pair(unwind, reg, save_offset))
        {
            if (save_offset != unwind->reg_offset[reg + 1] ||
                save_offset - WORD_SIZE != unwind->reg_offset[reg])
                break;
            save_offset -= DOUBLEWORD_ALIGNMENT;
            reg++;
        }
        else
        {
            if (save_offset != unwind->reg_offset[reg])
                break;
            save_offset -= WORD_SIZE;
        }
    }
    
    return (reg == TIC6X_NUM_UNWIND_REGS) ? reg_saved_mask : 0;
}

static bool is_register_pair(tic6x_unwind_info *unwind, int reg, int *reg2)
{
    if (reg >= TIC6X_NUM_UNWIND_REGS - 1)
    {
        *reg2 = -1;
        return false;
    }
    
    *reg2 = reg + 1;
    
    return unwind->reg_saved[*reg2]
        && tic6x_unwind_frame_regs[reg] == tic6x_unwind_frame_regs[*reg2] + 1
        && (tic6x_unwind_frame_regs[*reg2] & 1) == 0;
}

static bool verify_pair_offset(tic6x_unwind_info *unwind, int reg, int reg2, 
                               offsetT save_offset)
{
    int high_offset = target_big_endian ? WORD_SIZE : 0;
    
    return save_offset + WORD_SIZE - high_offset == unwind->reg_offset[reg]
        && save_offset + high_offset == unwind->reg_offset[reg2];
}

static unsigned check_compact_layout(tic6x_unwind_info *unwind, unsigned reg_saved_mask)
{
    offsetT save_offset = 0;
    int reg;
    
    if (!reg_saved_mask)
        return 0;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
        int reg2;
        
        if (!unwind->reg_saved[reg])
            continue;
        
        if (is_register_pair(unwind, reg, &reg2) && save_offset != 0)
        {
            if (!verify_pair_offset(unwind, reg, reg2, save_offset))
                break;
            reg++;
        }
        else
        {
            if (save_offset != unwind->reg_offset[reg])
                break;
        }
        save_offset -= DOUBLEWORD_ALIGNMENT;
    }
    
    return (reg == TIC6X_NUM_UNWIND_REGS) ? reg_saved_mask : 0;
}

static bool check_pop_rts_format(tic6x_unwind_info *unwind, unsigned reg_saved_mask)
{
    const int *pop_rts_offset;
    int reg;
    
    if (reg_saved_mask != POP_RTS_MASK)
        return false;
    
    pop_rts_offset = target_big_endian ? tic6x_pop_rts_offset_big 
                                       : tic6x_pop_rts_offset_little;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
        if (reg == UNWIND_B15)
            continue;
        
        if (unwind->reg_offset[reg] != pop_rts_offset[reg] * WORD_SIZE)
            return false;
    }
    
    return true;
}

static bool validate_manual_frame(tic6x_unwind_info *unwind, offsetT *save_offset)
{
    int reg;
    
    *save_offset = 0;
    
    for (reg = 0; reg < TIC6X_NUM_UNWIND_REGS; reg++)
    {
        if (!unwind->reg_saved[reg])
            continue;
        
        unwind->saved_reg_count++;
        
        if (unwind->reg_offset[reg] > 0 || 
            unwind->reg_offset[reg] < -MAX_SAVE_OFFSET ||
            (unwind->reg_offset[reg] & 3) != 0)
        {
            as_bad(_("stack frame layout too complex for unwinder"));
            return false;
        }
        
        if (unwind->reg_offset[reg] < *save_offset)
            *save_offset = unwind->reg_offset[reg] - WORD_SIZE;
    }
    
    *save_offset &= ~ALIGNMENT_MASK;
    return true;
}

void tic6x_cfi_endproc(struct fde_entry *fde)
{
    tic6x_unwind_info *unwind = tic6x_get_unwind();
    struct cfi_insn_data *insn;
    unsigned safe_mask = 0;
    unsigned compact_mask = 0;
    unsigned reg_saved_mask = 0;
    offsetT cfa_offset = 0;
    offsetT save_offset = 0;
    
    initialize_unwind_info(unwind);
    
    for (insn = fde->data; insn; insn = insn->next)
    {
        if (!process_cfi_instruction(unwind, insn, &cfa_offset))
            return;
    }
    
    if (!validate_cfa_settings(unwind, cfa_offset))
        return;
    
    reg_saved_mask = compute_reg_saved_mask(unwind);
    
    safe_mask = check_safe_debug_layout(unwind, reg_saved_mask);
    if (safe_mask)
        reg_saved_mask = 0;
    
    compact_mask = check_compact_layout(unwind, reg_saved_mask);
    if (compact_mask)
        reg_saved_mask = 0;
    
    if (check_pop_rts_format(unwind, reg_saved_mask))
    {
        unwind->pop_rts = true;
        reg_saved_mask = 0;
    }
    
    if (reg_saved_mask)
    {
        if (!validate_manual_frame(unwind, &save_offset))
            return;
    }
    
    if (unwind->cfa_reg == CFA_REG_SP && !reg_saved_mask)
    {
        cfa_offset += save_offset;
        if (cfa_offset < 0)
        {
            as_bad(_("unwound frame has negative size"));
            return;
        }
    }
    
    unwind->safe_mask = safe_mask;
    unwind->compact_mask = compact_mask;
    unwind->reg_saved_mask = reg_saved_mask;
    unwind->cfa_offset = cfa_offset;
    unwind->function_start = fde->start_address;
}
