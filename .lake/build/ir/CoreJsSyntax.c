// Lean compiler output
// Module: CoreJsSyntax
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_bool_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_bool_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_fid_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_fid_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_loc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_loc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqVal___boxed(lean_object*, lean_object*);
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CoreJS.Val.num"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__1_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__2_value;
static lean_once_cell_t lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3;
static lean_once_cell_t lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4;
static lean_once_cell_t lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CoreJS.Val.str"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__6 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__6_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__6_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__7 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__7_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__8 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__8_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.Val.bool"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__9 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__9_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__9_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__10 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__10_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__11 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__11_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CoreJS.Val.fid"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__12 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__12_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__12_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__13 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__13_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__14 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__14_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "CoreJS.Val.loc"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__15 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__15_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__15_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__16 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__16_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__17 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__17_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_modeljs__proofs_CoreJS_instReprVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_modeljs__proofs_CoreJS_instReprVal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_modeljs__proofs_CoreJS_instReprVal___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal___closed__0_value;
LEAN_EXPORT const lean_object* lp_modeljs__proofs_CoreJS_instReprVal = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprVal___closed__0_value;
static lean_once_cell_t lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instInhabitedVal_default;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instInhabitedVal;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_val_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_val_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqExpr___boxed(lean_object*, lean_object*);
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.Expr.val"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__1_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__2_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.Expr.var"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__3 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__3_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__3_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__4 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__4_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__5 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__5_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_modeljs__proofs_CoreJS_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_modeljs__proofs_CoreJS_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* lp_modeljs__proofs_CoreJS_instReprExpr = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprExpr___closed__0_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_BinOp_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqBinOp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqBinOp___boxed(lean_object*, lean_object*);
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.BinOp.add"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__1_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.BinOp.sub"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__2_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__2_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__3 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__3_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.BinOp.mul"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__4 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__4_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__4_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__5 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__5_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.BinOp.div"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__6 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__6_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__6_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__7 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__7_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.BinOp.eq"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__8 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__8_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__8_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__9 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__9_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.BinOp.lt"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__10 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__10_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__10_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__11 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__11_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.BinOp.le"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__12 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__12_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__12_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__13 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__13_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.BinOp.and"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__14 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__14_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__14_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__15 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__15_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.BinOp.or"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__16 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__16_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__16_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__17 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__17_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.BinOp.concat"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__18 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__18_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__18_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__19 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__19_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_modeljs__proofs_CoreJS_instReprBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_modeljs__proofs_CoreJS_instReprBinOp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp___closed__0_value;
LEAN_EXPORT const lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprBinOp___closed__0_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_skip_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_skip_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_assign_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_assign_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_binOp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_binOp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_objLit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_objLit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupS_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupS_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupD_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupD_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateS_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateS_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateD_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateD_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_call_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_call_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_seq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_seq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ifElse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ifElse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_whileDo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_whileDo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ret_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ret_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setTaint_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setTaint_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setSink_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setSink_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__0 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__1 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__1_value;
static const lean_string_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__2 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__2_value;
static const lean_string_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__3 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__3_value;
static const lean_ctor_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__3_value)}};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__4 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__4_value;
static const lean_ctor_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5_value;
static const lean_string_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__6 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__6_value;
static lean_once_cell_t lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7;
static lean_once_cell_t lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8;
static const lean_ctor_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__2_value)}};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__9 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__9_value;
static const lean_ctor_object lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__6_value)}};
static const lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__10 = (const lean_object*)&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg(lean_object*);
static const lean_string_object lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_string_object lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__1_value;
static lean_once_cell_t lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3;
static const lean_ctor_object lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__4 = (const lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__1_value)}};
static const lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.Stmt.skip"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__0_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__1_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CoreJS.Stmt.assign"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__2_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__2_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__3 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__3_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__4 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__4_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "CoreJS.Stmt.binOp"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__5 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__5_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__5_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__6 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__6_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__7 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__7_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CoreJS.Stmt.objLit"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__8 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__8_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__8_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__9 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__9_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__10 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__10_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.lookupS"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__11 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__11_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__11_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__12 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__12_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__13 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__13_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.lookupD"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__14 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__14_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__14_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__15 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__15_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__16 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__16_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.updateS"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__17 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__17_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__17_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__18 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__18_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__19 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__19_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.updateD"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__20 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__20_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__20_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__21 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__21_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__21_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__22 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__22_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "CoreJS.Stmt.call"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__23 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__23_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__23_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__24 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__24_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__24_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__25 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__25_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.Stmt.seq"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__26 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__26_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__26_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__27 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__27_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__27_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__28 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__28_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "CoreJS.Stmt.ifElse"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__29 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__29_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__29_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__30 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__30_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__30_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__31 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__31_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.whileDo"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__32 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__32_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__32_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__33 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__33_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__33_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__34 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__34_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CoreJS.Stmt.ret"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__35 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__35_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__35_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__36 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__36_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__36_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__37 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__37_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "CoreJS.Stmt.setTaint"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__38 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__38_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__38_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__39 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__39_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__39_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__40 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__40_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "CoreJS.Stmt.setSink"};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__41 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__41_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__41_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__42 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__42_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__42_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__43 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__43_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_modeljs__proofs_CoreJS_instReprStmt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_modeljs__proofs_CoreJS_instReprStmt_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt___closed__0_value;
LEAN_EXPORT const lean_object* lp_modeljs__proofs_CoreJS_instReprStmt = (const lean_object*)&lp_modeljs__proofs_CoreJS_instReprStmt___closed__0_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "CoreJS"};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__0_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_;;_"};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__1_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 217, 206, 129, 170, 116, 64, 93)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2_value_aux_0),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 9, 210, 97, 77, 201, 129, 147)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__3 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__3_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__4 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__4_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ;; "};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__5 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__5_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__5_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__6 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__6_value;
static const lean_string_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__7 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__7_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__8 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__8_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__8_value),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__9 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__9_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__4_value),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__6_value),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__9_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__10 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__10_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2_value),((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__10_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__11 = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__11_value;
LEAN_EXPORT const lean_object* lp_modeljs__proofs_CoreJS_term___x3b_x3b__ = (const lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__11_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__0_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__1_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__2 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__2_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__3 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__3_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_0),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_1),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value_aux_2),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Stmt.seq"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__5 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__5_value;
static lean_once_cell_t lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Stmt"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__7 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__7_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "seq"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__8 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__8_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(189, 15, 71, 201, 58, 13, 129, 158)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9_value_aux_0),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(17, 22, 216, 128, 252, 240, 62, 86)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 217, 206, 129, 170, 116, 64, 93)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value_aux_0),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(123, 155, 147, 74, 70, 78, 47, 77)}};
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value_aux_1),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 97, 64, 209, 105, 89, 97, 151)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__11 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__11_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__10_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__12 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__12_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__13 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__13_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__11_value),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__13_value)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__14 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__14_value;
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__15 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__15_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__16 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__16_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__0 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__0_value;
static const lean_ctor_object lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__1 = (const lean_object*)&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__1_value;
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_lits(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_lits___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_CoreJsSyntax_0__CoreJS_litsOfExprs(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_mapTR_loop___at___00CoreJS_Stmt_lits_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lits(lean_object*);
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_modeljs__proofs_CoreJS_Val_ctorIdx(v_x_7_);
lean_dec_ref(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
switch(lean_obj_tag(v_t_9_))
{
case 1:
{
lean_object* v_s_11_; lean_object* v___x_12_; 
v_s_11_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_s_11_);
lean_dec_ref_known(v_t_9_, 1);
v___x_12_ = lean_apply_1(v_k_10_, v_s_11_);
return v___x_12_;
}
case 2:
{
uint8_t v_b_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_b_13_ = lean_ctor_get_uint8(v_t_9_, 0);
lean_dec_ref_known(v_t_9_, 0);
v___x_14_ = lean_box(v_b_13_);
v___x_15_ = lean_apply_1(v_k_10_, v___x_14_);
return v___x_15_;
}
case 3:
{
lean_object* v_f_16_; lean_object* v___x_17_; 
v_f_16_ = lean_ctor_get(v_t_9_, 0);
lean_inc_ref(v_f_16_);
lean_dec_ref_known(v_t_9_, 1);
v___x_17_ = lean_apply_1(v_k_10_, v_f_16_);
return v___x_17_;
}
default: 
{
lean_object* v_n_18_; lean_object* v___x_19_; 
v_n_18_ = lean_ctor_get(v_t_9_, 0);
lean_inc(v_n_18_);
lean_dec_ref(v_t_9_);
v___x_19_ = lean_apply_1(v_k_10_, v_n_18_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_modeljs__proofs_CoreJS_Val_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_num_elim___redArg(lean_object* v_t_32_, lean_object* v_num_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_32_, v_num_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_num_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_num_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_36_, v_num_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_str_elim___redArg(lean_object* v_t_40_, lean_object* v_str_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_40_, v_str_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_str_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_str_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_44_, v_str_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_bool_elim___redArg(lean_object* v_t_48_, lean_object* v_bool_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_48_, v_bool_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_bool_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_bool_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_52_, v_bool_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_fid_elim___redArg(lean_object* v_t_56_, lean_object* v_fid_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_56_, v_fid_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_fid_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_fid_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_60_, v_fid_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_loc_elim___redArg(lean_object* v_t_64_, lean_object* v_loc_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_64_, v_loc_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Val_loc_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_loc_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lp_modeljs__proofs_CoreJS_Val_ctorElim___redArg(v_t_68_, v_loc_70_);
return v___x_71_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq(lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
switch(lean_obj_tag(v_x_72_))
{
case 0:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v_n_74_; lean_object* v_n_75_; uint8_t v___x_76_; 
v_n_74_ = lean_ctor_get(v_x_72_, 0);
v_n_75_ = lean_ctor_get(v_x_73_, 0);
v___x_76_ = lean_int_dec_eq(v_n_74_, v_n_75_);
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
case 1:
{
if (lean_obj_tag(v_x_73_) == 1)
{
lean_object* v_s_78_; lean_object* v_s_79_; uint8_t v___x_80_; 
v_s_78_ = lean_ctor_get(v_x_72_, 0);
v_s_79_ = lean_ctor_get(v_x_73_, 0);
v___x_80_ = lean_string_dec_eq(v_s_78_, v_s_79_);
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
case 2:
{
if (lean_obj_tag(v_x_73_) == 2)
{
uint8_t v_b_82_; 
v_b_82_ = lean_ctor_get_uint8(v_x_72_, 0);
if (v_b_82_ == 0)
{
uint8_t v_b_83_; 
v_b_83_ = lean_ctor_get_uint8(v_x_73_, 0);
if (v_b_83_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = 1;
return v___x_84_;
}
else
{
return v_b_82_;
}
}
else
{
uint8_t v_b_85_; 
v_b_85_ = lean_ctor_get_uint8(v_x_73_, 0);
return v_b_85_;
}
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
case 3:
{
if (lean_obj_tag(v_x_73_) == 3)
{
lean_object* v_f_87_; lean_object* v_f_88_; uint8_t v___x_89_; 
v_f_87_ = lean_ctor_get(v_x_72_, 0);
v_f_88_ = lean_ctor_get(v_x_73_, 0);
v___x_89_ = lean_string_dec_eq(v_f_87_, v_f_88_);
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
default: 
{
if (lean_obj_tag(v_x_73_) == 4)
{
lean_object* v_l_91_; lean_object* v_l_92_; uint8_t v___x_93_; 
v_l_91_ = lean_ctor_get(v_x_72_, 0);
v_l_92_ = lean_ctor_get(v_x_73_, 0);
v___x_93_ = lean_nat_dec_eq(v_l_91_, v_l_92_);
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq___boxed(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq(v_x_95_, v_x_96_);
lean_dec_ref(v_x_96_);
lean_dec_ref(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqVal(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq(v_x_99_, v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqVal___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = lp_modeljs__proofs_CoreJS_instDecidableEqVal(v_x_102_, v_x_103_);
lean_dec_ref(v_x_103_);
lean_dec_ref(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_nat_to_int(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_nat_to_int(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_to_int(v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr(lean_object* v_x_142_, lean_object* v_prec_143_){
_start:
{
lean_object* v___y_145_; lean_object* v___y_146_; lean_object* v___y_147_; 
switch(lean_obj_tag(v_x_142_))
{
case 0:
{
lean_object* v_n_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_176_; 
v_n_153_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_176_ == 0)
{
v___x_155_ = v_x_142_;
v_isShared_156_ = v_isSharedCheck_176_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_n_153_);
lean_dec(v_x_142_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_176_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___y_158_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_143_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_158_ = v___x_174_;
goto v___jp_157_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_158_ = v___x_175_;
goto v___jp_157_;
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_159_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__2));
v___x_160_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3);
v___x_161_ = lean_int_dec_lt(v_n_153_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = l_Int_repr(v_n_153_);
lean_dec(v_n_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 3);
lean_ctor_set(v___x_155_, 0, v___x_162_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
v___y_145_ = v___y_158_;
v___y_146_ = v___x_159_;
v___y_147_ = v___x_164_;
goto v___jp_144_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_unsigned_to_nat(1024u);
v___x_167_ = l_Int_repr(v_n_153_);
lean_dec(v_n_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 3);
lean_ctor_set(v___x_155_, 0, v___x_167_);
v___x_169_ = v___x_155_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = l_Repr_addAppParen(v___x_169_, v___x_166_);
v___y_145_ = v___y_158_;
v___y_146_ = v___x_159_;
v___y_147_ = v___x_170_;
goto v___jp_144_;
}
}
}
}
}
case 1:
{
lean_object* v_s_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_197_; 
v_s_177_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_197_ == 0)
{
v___x_179_ = v_x_142_;
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_s_177_);
lean_dec(v_x_142_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___y_182_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1024u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_prec_143_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_182_ = v___x_195_;
goto v___jp_181_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__8));
v___x_184_ = l_String_quote(v_s_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 3);
lean_ctor_set(v___x_179_, 0, v___x_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_192_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_183_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc(v___y_182_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_182_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_143_);
return v___x_191_;
}
}
}
}
case 2:
{
uint8_t v_b_198_; lean_object* v___y_200_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_b_198_ = lean_ctor_get_uint8(v_x_142_, 0);
lean_dec_ref_known(v_x_142_, 0);
v___x_208_ = lean_unsigned_to_nat(1024u);
v___x_209_ = lean_nat_dec_le(v___x_208_, v_prec_143_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_200_ = v___x_210_;
goto v___jp_199_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_200_ = v___x_211_;
goto v___jp_199_;
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_201_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__11));
v___x_202_ = l_Bool_repr___redArg(v_b_198_);
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
lean_inc(v___y_200_);
v___x_204_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_204_, 0, v___y_200_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_205_);
v___x_207_ = l_Repr_addAppParen(v___x_206_, v_prec_143_);
return v___x_207_;
}
}
case 3:
{
lean_object* v_f_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_232_; 
v_f_212_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_232_ == 0)
{
v___x_214_ = v_x_142_;
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_f_212_);
lean_dec(v_x_142_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___y_217_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(1024u);
v___x_229_ = lean_nat_dec_le(v___x_228_, v_prec_143_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_217_ = v___x_230_;
goto v___jp_216_;
}
else
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_217_ = v___x_231_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_218_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__14));
v___x_219_ = l_String_quote(v_f_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_219_);
v___x_221_ = v___x_214_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_227_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_218_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
lean_inc(v___y_217_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___y_217_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = 0;
v___x_225_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = l_Repr_addAppParen(v___x_225_, v_prec_143_);
return v___x_226_;
}
}
}
}
default: 
{
lean_object* v_l_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_253_; 
v_l_233_ = lean_ctor_get(v_x_142_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_253_ == 0)
{
v___x_235_ = v_x_142_;
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_l_233_);
lean_dec(v_x_142_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___y_238_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1024u);
v___x_250_ = lean_nat_dec_le(v___x_249_, v_prec_143_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_238_ = v___x_251_;
goto v___jp_237_;
}
else
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_238_ = v___x_252_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__17));
v___x_240_ = l_Nat_reprFast(v_l_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 3);
lean_ctor_set(v___x_235_, 0, v___x_240_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_248_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_239_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
lean_inc(v___y_238_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___y_238_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = 0;
v___x_246_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*1, v___x_245_);
v___x_247_ = l_Repr_addAppParen(v___x_246_, v_prec_143_);
return v___x_247_;
}
}
}
}
}
v___jp_144_:
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc(v___y_146_);
v___x_148_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_146_);
lean_ctor_set(v___x_148_, 1, v___y_147_);
lean_inc(v___y_145_);
v___x_149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_149_, 0, v___y_145_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = 0;
v___x_151_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*1, v___x_150_);
v___x_152_ = l_Repr_addAppParen(v___x_151_, v_prec_143_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprVal_repr___boxed(lean_object* v_x_254_, lean_object* v_prec_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_modeljs__proofs_CoreJS_instReprVal_repr(v_x_254_, v_prec_255_);
lean_dec(v_prec_255_);
return v_res_256_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__3);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instInhabitedVal_default(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0, &lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0_once, _init_lp_modeljs__proofs_CoreJS_instInhabitedVal_default___closed__0);
return v___x_261_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS_instInhabitedVal(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lp_modeljs__proofs_CoreJS_instInhabitedVal_default;
return v___x_262_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorIdx(lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(1u);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorIdx___boxed(lean_object* v_x_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = lp_modeljs__proofs_CoreJS_Expr_ctorIdx(v_x_266_);
lean_dec_ref(v_x_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(lean_object* v_t_268_, lean_object* v_k_269_){
_start:
{
lean_object* v_v_270_; lean_object* v___x_271_; 
v_v_270_ = lean_ctor_get(v_t_268_, 0);
lean_inc_ref(v_v_270_);
lean_dec_ref(v_t_268_);
v___x_271_ = lean_apply_1(v_k_269_, v_v_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim(lean_object* v_motive_272_, lean_object* v_ctorIdx_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_k_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(v_t_274_, v_k_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_ctorElim___boxed(lean_object* v_motive_278_, lean_object* v_ctorIdx_279_, lean_object* v_t_280_, lean_object* v_h_281_, lean_object* v_k_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim(v_motive_278_, v_ctorIdx_279_, v_t_280_, v_h_281_, v_k_282_);
lean_dec(v_ctorIdx_279_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_val_elim___redArg(lean_object* v_t_284_, lean_object* v_val_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(v_t_284_, v_val_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_val_elim(lean_object* v_motive_287_, lean_object* v_t_288_, lean_object* v_h_289_, lean_object* v_val_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(v_t_288_, v_val_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_var_elim___redArg(lean_object* v_t_292_, lean_object* v_var_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(v_t_292_, v_var_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_var_elim(lean_object* v_motive_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_var_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lp_modeljs__proofs_CoreJS_Expr_ctorElim___redArg(v_t_296_, v_var_298_);
return v___x_299_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_v_302_; lean_object* v_v_303_; uint8_t v___x_304_; 
v_v_302_ = lean_ctor_get(v_x_300_, 0);
v_v_303_ = lean_ctor_get(v_x_301_, 0);
v___x_304_ = lp_modeljs__proofs_CoreJS_instDecidableEqVal_decEq(v_v_302_, v_v_303_);
return v___x_304_;
}
else
{
uint8_t v___x_305_; 
v___x_305_ = 0;
return v___x_305_;
}
}
else
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_306_; 
v___x_306_ = 0;
return v___x_306_;
}
else
{
lean_object* v_x_307_; lean_object* v_x_308_; uint8_t v___x_309_; 
v_x_307_ = lean_ctor_get(v_x_300_, 0);
v_x_308_ = lean_ctor_get(v_x_301_, 0);
v___x_309_ = lean_string_dec_eq(v_x_307_, v_x_308_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq___boxed(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq(v_x_310_, v_x_311_);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqExpr(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lp_modeljs__proofs_CoreJS_instDecidableEqExpr_decEq(v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqExpr___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = lp_modeljs__proofs_CoreJS_instDecidableEqExpr(v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr(lean_object* v_x_333_, lean_object* v_prec_334_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v_v_335_; lean_object* v___y_337_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_v_335_ = lean_ctor_get(v_x_333_, 0);
lean_inc_ref(v_v_335_);
lean_dec_ref_known(v_x_333_, 1);
v___x_346_ = lean_unsigned_to_nat(1024u);
v___x_347_ = lean_nat_dec_le(v___x_346_, v_prec_334_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_337_ = v___x_348_;
goto v___jp_336_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_337_ = v___x_349_;
goto v___jp_336_;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_338_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__2));
v___x_339_ = lean_unsigned_to_nat(1024u);
v___x_340_ = lp_modeljs__proofs_CoreJS_instReprVal_repr(v_v_335_, v___x_339_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_338_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc(v___y_337_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___y_337_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = 0;
v___x_344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
v___x_345_ = l_Repr_addAppParen(v___x_344_, v_prec_334_);
return v___x_345_;
}
}
else
{
lean_object* v_x_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_370_; 
v_x_350_ = lean_ctor_get(v_x_333_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_333_);
if (v_isSharedCheck_370_ == 0)
{
v___x_352_ = v_x_333_;
v_isShared_353_ = v_isSharedCheck_370_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_x_350_);
lean_dec(v_x_333_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_370_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___y_355_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(1024u);
v___x_367_ = lean_nat_dec_le(v___x_366_, v_prec_334_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_355_ = v___x_368_;
goto v___jp_354_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_355_ = v___x_369_;
goto v___jp_354_;
}
v___jp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_356_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprExpr_repr___closed__5));
v___x_357_ = l_String_quote(v_x_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set_tag(v___x_352_, 3);
lean_ctor_set(v___x_352_, 0, v___x_357_);
v___x_359_ = v___x_352_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_365_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_356_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
lean_inc(v___y_355_);
v___x_361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_361_, 0, v___y_355_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*1, v___x_362_);
v___x_364_ = l_Repr_addAppParen(v___x_363_, v_prec_334_);
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprExpr_repr___boxed(lean_object* v_x_371_, lean_object* v_prec_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_x_371_, v_prec_372_);
lean_dec(v_prec_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(uint8_t v_x_376_){
_start:
{
switch(v_x_376_)
{
case 0:
{
lean_object* v___x_377_; 
v___x_377_ = lean_unsigned_to_nat(0u);
return v___x_377_;
}
case 1:
{
lean_object* v___x_378_; 
v___x_378_ = lean_unsigned_to_nat(1u);
return v___x_378_;
}
case 2:
{
lean_object* v___x_379_; 
v___x_379_ = lean_unsigned_to_nat(2u);
return v___x_379_;
}
case 3:
{
lean_object* v___x_380_; 
v___x_380_ = lean_unsigned_to_nat(3u);
return v___x_380_;
}
case 4:
{
lean_object* v___x_381_; 
v___x_381_ = lean_unsigned_to_nat(4u);
return v___x_381_;
}
case 5:
{
lean_object* v___x_382_; 
v___x_382_ = lean_unsigned_to_nat(5u);
return v___x_382_;
}
case 6:
{
lean_object* v___x_383_; 
v___x_383_ = lean_unsigned_to_nat(6u);
return v___x_383_;
}
case 7:
{
lean_object* v___x_384_; 
v___x_384_ = lean_unsigned_to_nat(7u);
return v___x_384_;
}
case 8:
{
lean_object* v___x_385_; 
v___x_385_ = lean_unsigned_to_nat(8u);
return v___x_385_;
}
default: 
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(9u);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorIdx___boxed(lean_object* v_x_387_){
_start:
{
uint8_t v_x_boxed_388_; lean_object* v_res_389_; 
v_x_boxed_388_ = lean_unbox(v_x_387_);
v_res_389_ = lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(v_x_boxed_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_toCtorIdx(uint8_t v_x_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_toCtorIdx___boxed(lean_object* v_x_392_){
_start:
{
uint8_t v_x_4__boxed_393_; lean_object* v_res_394_; 
v_x_4__boxed_393_ = lean_unbox(v_x_392_);
v_res_394_ = lp_modeljs__proofs_CoreJS_BinOp_toCtorIdx(v_x_4__boxed_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___redArg(lean_object* v_k_395_){
_start:
{
lean_inc(v_k_395_);
return v_k_395_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___redArg___boxed(lean_object* v_k_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = lp_modeljs__proofs_CoreJS_BinOp_ctorElim___redArg(v_k_396_);
lean_dec(v_k_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim(lean_object* v_motive_398_, lean_object* v_ctorIdx_399_, uint8_t v_t_400_, lean_object* v_h_401_, lean_object* v_k_402_){
_start:
{
lean_inc(v_k_402_);
return v_k_402_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ctorElim___boxed(lean_object* v_motive_403_, lean_object* v_ctorIdx_404_, lean_object* v_t_405_, lean_object* v_h_406_, lean_object* v_k_407_){
_start:
{
uint8_t v_t_boxed_408_; lean_object* v_res_409_; 
v_t_boxed_408_ = lean_unbox(v_t_405_);
v_res_409_ = lp_modeljs__proofs_CoreJS_BinOp_ctorElim(v_motive_403_, v_ctorIdx_404_, v_t_boxed_408_, v_h_406_, v_k_407_);
lean_dec(v_k_407_);
lean_dec(v_ctorIdx_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___redArg(lean_object* v_add_410_){
_start:
{
lean_inc(v_add_410_);
return v_add_410_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___redArg___boxed(lean_object* v_add_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = lp_modeljs__proofs_CoreJS_BinOp_add_elim___redArg(v_add_411_);
lean_dec(v_add_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim(lean_object* v_motive_413_, uint8_t v_t_414_, lean_object* v_h_415_, lean_object* v_add_416_){
_start:
{
lean_inc(v_add_416_);
return v_add_416_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_add_elim___boxed(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_add_420_){
_start:
{
uint8_t v_t_boxed_421_; lean_object* v_res_422_; 
v_t_boxed_421_ = lean_unbox(v_t_418_);
v_res_422_ = lp_modeljs__proofs_CoreJS_BinOp_add_elim(v_motive_417_, v_t_boxed_421_, v_h_419_, v_add_420_);
lean_dec(v_add_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___redArg(lean_object* v_sub_423_){
_start:
{
lean_inc(v_sub_423_);
return v_sub_423_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___redArg___boxed(lean_object* v_sub_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = lp_modeljs__proofs_CoreJS_BinOp_sub_elim___redArg(v_sub_424_);
lean_dec(v_sub_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim(lean_object* v_motive_426_, uint8_t v_t_427_, lean_object* v_h_428_, lean_object* v_sub_429_){
_start:
{
lean_inc(v_sub_429_);
return v_sub_429_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_sub_elim___boxed(lean_object* v_motive_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_sub_433_){
_start:
{
uint8_t v_t_boxed_434_; lean_object* v_res_435_; 
v_t_boxed_434_ = lean_unbox(v_t_431_);
v_res_435_ = lp_modeljs__proofs_CoreJS_BinOp_sub_elim(v_motive_430_, v_t_boxed_434_, v_h_432_, v_sub_433_);
lean_dec(v_sub_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___redArg(lean_object* v_mul_436_){
_start:
{
lean_inc(v_mul_436_);
return v_mul_436_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___redArg___boxed(lean_object* v_mul_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = lp_modeljs__proofs_CoreJS_BinOp_mul_elim___redArg(v_mul_437_);
lean_dec(v_mul_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim(lean_object* v_motive_439_, uint8_t v_t_440_, lean_object* v_h_441_, lean_object* v_mul_442_){
_start:
{
lean_inc(v_mul_442_);
return v_mul_442_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_mul_elim___boxed(lean_object* v_motive_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_mul_446_){
_start:
{
uint8_t v_t_boxed_447_; lean_object* v_res_448_; 
v_t_boxed_447_ = lean_unbox(v_t_444_);
v_res_448_ = lp_modeljs__proofs_CoreJS_BinOp_mul_elim(v_motive_443_, v_t_boxed_447_, v_h_445_, v_mul_446_);
lean_dec(v_mul_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___redArg(lean_object* v_div_449_){
_start:
{
lean_inc(v_div_449_);
return v_div_449_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___redArg___boxed(lean_object* v_div_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = lp_modeljs__proofs_CoreJS_BinOp_div_elim___redArg(v_div_450_);
lean_dec(v_div_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim(lean_object* v_motive_452_, uint8_t v_t_453_, lean_object* v_h_454_, lean_object* v_div_455_){
_start:
{
lean_inc(v_div_455_);
return v_div_455_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_div_elim___boxed(lean_object* v_motive_456_, lean_object* v_t_457_, lean_object* v_h_458_, lean_object* v_div_459_){
_start:
{
uint8_t v_t_boxed_460_; lean_object* v_res_461_; 
v_t_boxed_460_ = lean_unbox(v_t_457_);
v_res_461_ = lp_modeljs__proofs_CoreJS_BinOp_div_elim(v_motive_456_, v_t_boxed_460_, v_h_458_, v_div_459_);
lean_dec(v_div_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___redArg(lean_object* v_eq_462_){
_start:
{
lean_inc(v_eq_462_);
return v_eq_462_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___redArg___boxed(lean_object* v_eq_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = lp_modeljs__proofs_CoreJS_BinOp_eq_elim___redArg(v_eq_463_);
lean_dec(v_eq_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim(lean_object* v_motive_465_, uint8_t v_t_466_, lean_object* v_h_467_, lean_object* v_eq_468_){
_start:
{
lean_inc(v_eq_468_);
return v_eq_468_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_eq_elim___boxed(lean_object* v_motive_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_eq_472_){
_start:
{
uint8_t v_t_boxed_473_; lean_object* v_res_474_; 
v_t_boxed_473_ = lean_unbox(v_t_470_);
v_res_474_ = lp_modeljs__proofs_CoreJS_BinOp_eq_elim(v_motive_469_, v_t_boxed_473_, v_h_471_, v_eq_472_);
lean_dec(v_eq_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___redArg(lean_object* v_lt_475_){
_start:
{
lean_inc(v_lt_475_);
return v_lt_475_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___redArg___boxed(lean_object* v_lt_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = lp_modeljs__proofs_CoreJS_BinOp_lt_elim___redArg(v_lt_476_);
lean_dec(v_lt_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim(lean_object* v_motive_478_, uint8_t v_t_479_, lean_object* v_h_480_, lean_object* v_lt_481_){
_start:
{
lean_inc(v_lt_481_);
return v_lt_481_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_lt_elim___boxed(lean_object* v_motive_482_, lean_object* v_t_483_, lean_object* v_h_484_, lean_object* v_lt_485_){
_start:
{
uint8_t v_t_boxed_486_; lean_object* v_res_487_; 
v_t_boxed_486_ = lean_unbox(v_t_483_);
v_res_487_ = lp_modeljs__proofs_CoreJS_BinOp_lt_elim(v_motive_482_, v_t_boxed_486_, v_h_484_, v_lt_485_);
lean_dec(v_lt_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___redArg(lean_object* v_le_488_){
_start:
{
lean_inc(v_le_488_);
return v_le_488_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___redArg___boxed(lean_object* v_le_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = lp_modeljs__proofs_CoreJS_BinOp_le_elim___redArg(v_le_489_);
lean_dec(v_le_489_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim(lean_object* v_motive_491_, uint8_t v_t_492_, lean_object* v_h_493_, lean_object* v_le_494_){
_start:
{
lean_inc(v_le_494_);
return v_le_494_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_le_elim___boxed(lean_object* v_motive_495_, lean_object* v_t_496_, lean_object* v_h_497_, lean_object* v_le_498_){
_start:
{
uint8_t v_t_boxed_499_; lean_object* v_res_500_; 
v_t_boxed_499_ = lean_unbox(v_t_496_);
v_res_500_ = lp_modeljs__proofs_CoreJS_BinOp_le_elim(v_motive_495_, v_t_boxed_499_, v_h_497_, v_le_498_);
lean_dec(v_le_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___redArg(lean_object* v_and_501_){
_start:
{
lean_inc(v_and_501_);
return v_and_501_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___redArg___boxed(lean_object* v_and_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = lp_modeljs__proofs_CoreJS_BinOp_and_elim___redArg(v_and_502_);
lean_dec(v_and_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim(lean_object* v_motive_504_, uint8_t v_t_505_, lean_object* v_h_506_, lean_object* v_and_507_){
_start:
{
lean_inc(v_and_507_);
return v_and_507_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_and_elim___boxed(lean_object* v_motive_508_, lean_object* v_t_509_, lean_object* v_h_510_, lean_object* v_and_511_){
_start:
{
uint8_t v_t_boxed_512_; lean_object* v_res_513_; 
v_t_boxed_512_ = lean_unbox(v_t_509_);
v_res_513_ = lp_modeljs__proofs_CoreJS_BinOp_and_elim(v_motive_508_, v_t_boxed_512_, v_h_510_, v_and_511_);
lean_dec(v_and_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___redArg(lean_object* v_or_514_){
_start:
{
lean_inc(v_or_514_);
return v_or_514_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___redArg___boxed(lean_object* v_or_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = lp_modeljs__proofs_CoreJS_BinOp_or_elim___redArg(v_or_515_);
lean_dec(v_or_515_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim(lean_object* v_motive_517_, uint8_t v_t_518_, lean_object* v_h_519_, lean_object* v_or_520_){
_start:
{
lean_inc(v_or_520_);
return v_or_520_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_or_elim___boxed(lean_object* v_motive_521_, lean_object* v_t_522_, lean_object* v_h_523_, lean_object* v_or_524_){
_start:
{
uint8_t v_t_boxed_525_; lean_object* v_res_526_; 
v_t_boxed_525_ = lean_unbox(v_t_522_);
v_res_526_ = lp_modeljs__proofs_CoreJS_BinOp_or_elim(v_motive_521_, v_t_boxed_525_, v_h_523_, v_or_524_);
lean_dec(v_or_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___redArg(lean_object* v_concat_527_){
_start:
{
lean_inc(v_concat_527_);
return v_concat_527_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___redArg___boxed(lean_object* v_concat_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = lp_modeljs__proofs_CoreJS_BinOp_concat_elim___redArg(v_concat_528_);
lean_dec(v_concat_528_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim(lean_object* v_motive_530_, uint8_t v_t_531_, lean_object* v_h_532_, lean_object* v_concat_533_){
_start:
{
lean_inc(v_concat_533_);
return v_concat_533_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_concat_elim___boxed(lean_object* v_motive_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_concat_537_){
_start:
{
uint8_t v_t_boxed_538_; lean_object* v_res_539_; 
v_t_boxed_538_ = lean_unbox(v_t_535_);
v_res_539_ = lp_modeljs__proofs_CoreJS_BinOp_concat_elim(v_motive_534_, v_t_boxed_538_, v_h_536_, v_concat_537_);
lean_dec(v_concat_537_);
return v_res_539_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_BinOp_ofNat(lean_object* v_n_540_){
_start:
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_unsigned_to_nat(4u);
v___x_542_ = lean_nat_dec_le(v_n_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(6u);
v___x_544_ = lean_nat_dec_le(v_n_540_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(7u);
v___x_546_ = lean_nat_dec_le(v_n_540_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(8u);
v___x_548_ = lean_nat_dec_le(v_n_540_, v___x_547_);
if (v___x_548_ == 0)
{
uint8_t v___x_549_; 
v___x_549_ = 9;
return v___x_549_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = 8;
return v___x_550_;
}
}
else
{
uint8_t v___x_551_; 
v___x_551_ = 7;
return v___x_551_;
}
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_unsigned_to_nat(5u);
v___x_553_ = lean_nat_dec_le(v_n_540_, v___x_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 6;
return v___x_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = 5;
return v___x_555_;
}
}
}
else
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_dec_le(v_n_540_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = lean_unsigned_to_nat(2u);
v___x_559_ = lean_nat_dec_le(v_n_540_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(3u);
v___x_561_ = lean_nat_dec_le(v_n_540_, v___x_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; 
v___x_562_ = 4;
return v___x_562_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = 3;
return v___x_563_;
}
}
else
{
uint8_t v___x_564_; 
v___x_564_ = 2;
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_le(v_n_540_, v___x_565_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 1;
return v___x_567_;
}
else
{
uint8_t v___x_568_; 
v___x_568_ = 0;
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_BinOp_ofNat___boxed(lean_object* v_n_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = lp_modeljs__proofs_CoreJS_BinOp_ofNat(v_n_569_);
lean_dec(v_n_569_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT uint8_t lp_modeljs__proofs_CoreJS_instDecidableEqBinOp(uint8_t v_x_572_, uint8_t v_y_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(v_x_572_);
v___x_575_ = lp_modeljs__proofs_CoreJS_BinOp_ctorIdx(v_y_573_);
v___x_576_ = lean_nat_dec_eq(v___x_574_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v___x_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instDecidableEqBinOp___boxed(lean_object* v_x_577_, lean_object* v_y_578_){
_start:
{
uint8_t v_x_13__boxed_579_; uint8_t v_y_14__boxed_580_; uint8_t v_res_581_; lean_object* v_r_582_; 
v_x_13__boxed_579_ = lean_unbox(v_x_577_);
v_y_14__boxed_580_ = lean_unbox(v_y_578_);
v_res_581_ = lp_modeljs__proofs_CoreJS_instDecidableEqBinOp(v_x_13__boxed_579_, v_y_14__boxed_580_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr(uint8_t v_x_613_, lean_object* v_prec_614_){
_start:
{
lean_object* v___y_616_; lean_object* v___y_623_; lean_object* v___y_630_; lean_object* v___y_637_; lean_object* v___y_644_; lean_object* v___y_651_; lean_object* v___y_658_; lean_object* v___y_665_; lean_object* v___y_672_; lean_object* v___y_679_; 
switch(v_x_613_)
{
case 0:
{
lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(1024u);
v___x_686_ = lean_nat_dec_le(v___x_685_, v_prec_614_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_616_ = v___x_687_;
goto v___jp_615_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_616_ = v___x_688_;
goto v___jp_615_;
}
}
case 1:
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_unsigned_to_nat(1024u);
v___x_690_ = lean_nat_dec_le(v___x_689_, v_prec_614_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_623_ = v___x_691_;
goto v___jp_622_;
}
else
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_623_ = v___x_692_;
goto v___jp_622_;
}
}
case 2:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(1024u);
v___x_694_ = lean_nat_dec_le(v___x_693_, v_prec_614_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_630_ = v___x_695_;
goto v___jp_629_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_630_ = v___x_696_;
goto v___jp_629_;
}
}
case 3:
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = lean_unsigned_to_nat(1024u);
v___x_698_ = lean_nat_dec_le(v___x_697_, v_prec_614_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_637_ = v___x_699_;
goto v___jp_636_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_637_ = v___x_700_;
goto v___jp_636_;
}
}
case 4:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_unsigned_to_nat(1024u);
v___x_702_ = lean_nat_dec_le(v___x_701_, v_prec_614_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_644_ = v___x_703_;
goto v___jp_643_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_644_ = v___x_704_;
goto v___jp_643_;
}
}
case 5:
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_unsigned_to_nat(1024u);
v___x_706_ = lean_nat_dec_le(v___x_705_, v_prec_614_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_651_ = v___x_707_;
goto v___jp_650_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_651_ = v___x_708_;
goto v___jp_650_;
}
}
case 6:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(1024u);
v___x_710_ = lean_nat_dec_le(v___x_709_, v_prec_614_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_658_ = v___x_711_;
goto v___jp_657_;
}
else
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_658_ = v___x_712_;
goto v___jp_657_;
}
}
case 7:
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(1024u);
v___x_714_ = lean_nat_dec_le(v___x_713_, v_prec_614_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_665_ = v___x_715_;
goto v___jp_664_;
}
else
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_665_ = v___x_716_;
goto v___jp_664_;
}
}
case 8:
{
lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_717_ = lean_unsigned_to_nat(1024u);
v___x_718_ = lean_nat_dec_le(v___x_717_, v_prec_614_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_672_ = v___x_719_;
goto v___jp_671_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_672_ = v___x_720_;
goto v___jp_671_;
}
}
default: 
{
lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_unsigned_to_nat(1024u);
v___x_722_ = lean_nat_dec_le(v___x_721_, v_prec_614_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_679_ = v___x_723_;
goto v___jp_678_;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_679_ = v___x_724_;
goto v___jp_678_;
}
}
}
v___jp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_617_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__1));
lean_inc(v___y_616_);
v___x_618_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_618_, 0, v___y_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v___x_619_ = 0;
v___x_620_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*1, v___x_619_);
v___x_621_ = l_Repr_addAppParen(v___x_620_, v_prec_614_);
return v___x_621_;
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_624_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__3));
lean_inc(v___y_623_);
v___x_625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_625_, 0, v___y_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = 0;
v___x_627_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*1, v___x_626_);
v___x_628_ = l_Repr_addAppParen(v___x_627_, v_prec_614_);
return v___x_628_;
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__5));
lean_inc(v___y_630_);
v___x_632_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_632_, 0, v___y_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = 0;
v___x_634_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*1, v___x_633_);
v___x_635_ = l_Repr_addAppParen(v___x_634_, v_prec_614_);
return v___x_635_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_638_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__7));
lean_inc(v___y_637_);
v___x_639_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = 0;
v___x_641_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*1, v___x_640_);
v___x_642_ = l_Repr_addAppParen(v___x_641_, v_prec_614_);
return v___x_642_;
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_645_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__9));
lean_inc(v___y_644_);
v___x_646_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_646_, 0, v___y_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = 0;
v___x_648_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v___x_647_);
v___x_649_ = l_Repr_addAppParen(v___x_648_, v_prec_614_);
return v___x_649_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_652_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__11));
lean_inc(v___y_651_);
v___x_653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_653_, 0, v___y_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = 0;
v___x_655_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*1, v___x_654_);
v___x_656_ = l_Repr_addAppParen(v___x_655_, v_prec_614_);
return v___x_656_;
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_659_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__13));
lean_inc(v___y_658_);
v___x_660_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_660_, 0, v___y_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = 0;
v___x_662_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*1, v___x_661_);
v___x_663_ = l_Repr_addAppParen(v___x_662_, v_prec_614_);
return v___x_663_;
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_666_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__15));
lean_inc(v___y_665_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = 0;
v___x_669_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_669_, 0, v___x_667_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*1, v___x_668_);
v___x_670_ = l_Repr_addAppParen(v___x_669_, v_prec_614_);
return v___x_670_;
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_673_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__17));
lean_inc(v___y_672_);
v___x_674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_674_, 0, v___y_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = 0;
v___x_676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*1, v___x_675_);
v___x_677_ = l_Repr_addAppParen(v___x_676_, v_prec_614_);
return v___x_677_;
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_680_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprBinOp_repr___closed__19));
lean_inc(v___y_679_);
v___x_681_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_681_, 0, v___y_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = 0;
v___x_683_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*1, v___x_682_);
v___x_684_ = l_Repr_addAppParen(v___x_683_, v_prec_614_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprBinOp_repr___boxed(lean_object* v_x_725_, lean_object* v_prec_726_){
_start:
{
uint8_t v_x_565__boxed_727_; lean_object* v_res_728_; 
v_x_565__boxed_727_ = lean_unbox(v_x_725_);
v_res_728_ = lp_modeljs__proofs_CoreJS_instReprBinOp_repr(v_x_565__boxed_727_, v_prec_726_);
lean_dec(v_prec_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorIdx(lean_object* v_x_731_){
_start:
{
switch(lean_obj_tag(v_x_731_))
{
case 0:
{
lean_object* v___x_732_; 
v___x_732_ = lean_unsigned_to_nat(0u);
return v___x_732_;
}
case 1:
{
lean_object* v___x_733_; 
v___x_733_ = lean_unsigned_to_nat(1u);
return v___x_733_;
}
case 2:
{
lean_object* v___x_734_; 
v___x_734_ = lean_unsigned_to_nat(2u);
return v___x_734_;
}
case 3:
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(3u);
return v___x_735_;
}
case 4:
{
lean_object* v___x_736_; 
v___x_736_ = lean_unsigned_to_nat(4u);
return v___x_736_;
}
case 5:
{
lean_object* v___x_737_; 
v___x_737_ = lean_unsigned_to_nat(5u);
return v___x_737_;
}
case 6:
{
lean_object* v___x_738_; 
v___x_738_ = lean_unsigned_to_nat(6u);
return v___x_738_;
}
case 7:
{
lean_object* v___x_739_; 
v___x_739_ = lean_unsigned_to_nat(7u);
return v___x_739_;
}
case 8:
{
lean_object* v___x_740_; 
v___x_740_ = lean_unsigned_to_nat(8u);
return v___x_740_;
}
case 9:
{
lean_object* v___x_741_; 
v___x_741_ = lean_unsigned_to_nat(9u);
return v___x_741_;
}
case 10:
{
lean_object* v___x_742_; 
v___x_742_ = lean_unsigned_to_nat(10u);
return v___x_742_;
}
case 11:
{
lean_object* v___x_743_; 
v___x_743_ = lean_unsigned_to_nat(11u);
return v___x_743_;
}
case 12:
{
lean_object* v___x_744_; 
v___x_744_ = lean_unsigned_to_nat(12u);
return v___x_744_;
}
case 13:
{
lean_object* v___x_745_; 
v___x_745_ = lean_unsigned_to_nat(13u);
return v___x_745_;
}
default: 
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(14u);
return v___x_746_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorIdx___boxed(lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = lp_modeljs__proofs_CoreJS_Stmt_ctorIdx(v_x_747_);
lean_dec(v_x_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(lean_object* v_t_749_, lean_object* v_k_750_){
_start:
{
switch(lean_obj_tag(v_t_749_))
{
case 0:
{
return v_k_750_;
}
case 1:
{
lean_object* v_x_751_; lean_object* v_e_752_; lean_object* v___x_753_; 
v_x_751_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_x_751_);
v_e_752_ = lean_ctor_get(v_t_749_, 1);
lean_inc_ref(v_e_752_);
lean_dec_ref_known(v_t_749_, 2);
v___x_753_ = lean_apply_2(v_k_750_, v_x_751_, v_e_752_);
return v___x_753_;
}
case 2:
{
lean_object* v_x_754_; lean_object* v_00_u03ba_755_; uint8_t v_op_756_; lean_object* v_e_u2081_757_; lean_object* v_e_u2082_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_x_754_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_x_754_);
v_00_u03ba_755_ = lean_ctor_get(v_t_749_, 1);
lean_inc(v_00_u03ba_755_);
v_op_756_ = lean_ctor_get_uint8(v_t_749_, sizeof(void*)*4);
v_e_u2081_757_ = lean_ctor_get(v_t_749_, 2);
lean_inc_ref(v_e_u2081_757_);
v_e_u2082_758_ = lean_ctor_get(v_t_749_, 3);
lean_inc_ref(v_e_u2082_758_);
lean_dec_ref_known(v_t_749_, 4);
v___x_759_ = lean_box(v_op_756_);
v___x_760_ = lean_apply_5(v_k_750_, v_x_754_, v_00_u03ba_755_, v___x_759_, v_e_u2081_757_, v_e_u2082_758_);
return v___x_760_;
}
case 3:
{
lean_object* v_x_761_; lean_object* v_00_u03ba_762_; lean_object* v_fs_763_; lean_object* v___x_764_; 
v_x_761_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_x_761_);
v_00_u03ba_762_ = lean_ctor_get(v_t_749_, 1);
lean_inc(v_00_u03ba_762_);
v_fs_763_ = lean_ctor_get(v_t_749_, 2);
lean_inc(v_fs_763_);
lean_dec_ref_known(v_t_749_, 3);
v___x_764_ = lean_apply_3(v_k_750_, v_x_761_, v_00_u03ba_762_, v_fs_763_);
return v___x_764_;
}
case 8:
{
lean_object* v_x_765_; lean_object* v_e_766_; lean_object* v_es_767_; lean_object* v___x_768_; 
v_x_765_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_x_765_);
v_e_766_ = lean_ctor_get(v_t_749_, 1);
lean_inc_ref(v_e_766_);
v_es_767_ = lean_ctor_get(v_t_749_, 2);
lean_inc(v_es_767_);
lean_dec_ref_known(v_t_749_, 3);
v___x_768_ = lean_apply_3(v_k_750_, v_x_765_, v_e_766_, v_es_767_);
return v___x_768_;
}
case 9:
{
lean_object* v_s_u2081_769_; lean_object* v_s_u2082_770_; lean_object* v___x_771_; 
v_s_u2081_769_ = lean_ctor_get(v_t_749_, 0);
lean_inc(v_s_u2081_769_);
v_s_u2082_770_ = lean_ctor_get(v_t_749_, 1);
lean_inc(v_s_u2082_770_);
lean_dec_ref_known(v_t_749_, 2);
v___x_771_ = lean_apply_2(v_k_750_, v_s_u2081_769_, v_s_u2082_770_);
return v___x_771_;
}
case 10:
{
lean_object* v_e_772_; lean_object* v_s_u2081_773_; lean_object* v_s_u2082_774_; lean_object* v___x_775_; 
v_e_772_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_e_772_);
v_s_u2081_773_ = lean_ctor_get(v_t_749_, 1);
lean_inc(v_s_u2081_773_);
v_s_u2082_774_ = lean_ctor_get(v_t_749_, 2);
lean_inc(v_s_u2082_774_);
lean_dec_ref_known(v_t_749_, 3);
v___x_775_ = lean_apply_3(v_k_750_, v_e_772_, v_s_u2081_773_, v_s_u2082_774_);
return v___x_775_;
}
case 11:
{
lean_object* v_e_776_; lean_object* v_s_777_; lean_object* v___x_778_; 
v_e_776_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_e_776_);
v_s_777_ = lean_ctor_get(v_t_749_, 1);
lean_inc(v_s_777_);
lean_dec_ref_known(v_t_749_, 2);
v___x_778_ = lean_apply_2(v_k_750_, v_e_776_, v_s_777_);
return v___x_778_;
}
case 12:
{
lean_object* v_e_779_; lean_object* v___x_780_; 
v_e_779_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_e_779_);
lean_dec_ref_known(v_t_749_, 1);
v___x_780_ = lean_apply_1(v_k_750_, v_e_779_);
return v___x_780_;
}
case 13:
{
lean_object* v_e_781_; lean_object* v___x_782_; 
v_e_781_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_e_781_);
lean_dec_ref_known(v_t_749_, 1);
v___x_782_ = lean_apply_1(v_k_750_, v_e_781_);
return v___x_782_;
}
case 14:
{
lean_object* v_e_783_; lean_object* v___x_784_; 
v_e_783_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_e_783_);
lean_dec_ref_known(v_t_749_, 1);
v___x_784_ = lean_apply_1(v_k_750_, v_e_783_);
return v___x_784_;
}
default: 
{
lean_object* v_x_785_; lean_object* v_e_786_; lean_object* v_p_787_; lean_object* v___x_788_; 
v_x_785_ = lean_ctor_get(v_t_749_, 0);
lean_inc_ref(v_x_785_);
v_e_786_ = lean_ctor_get(v_t_749_, 1);
lean_inc_ref(v_e_786_);
v_p_787_ = lean_ctor_get(v_t_749_, 2);
lean_inc_ref(v_p_787_);
lean_dec(v_t_749_);
v___x_788_ = lean_apply_3(v_k_750_, v_x_785_, v_e_786_, v_p_787_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim(lean_object* v_motive_789_, lean_object* v_ctorIdx_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_791_, v_k_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ctorElim___boxed(lean_object* v_motive_795_, lean_object* v_ctorIdx_796_, lean_object* v_t_797_, lean_object* v_h_798_, lean_object* v_k_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim(v_motive_795_, v_ctorIdx_796_, v_t_797_, v_h_798_, v_k_799_);
lean_dec(v_ctorIdx_796_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_skip_elim___redArg(lean_object* v_t_801_, lean_object* v_skip_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_801_, v_skip_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_skip_elim(lean_object* v_motive_804_, lean_object* v_t_805_, lean_object* v_h_806_, lean_object* v_skip_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_805_, v_skip_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_assign_elim___redArg(lean_object* v_t_809_, lean_object* v_assign_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_809_, v_assign_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_assign_elim(lean_object* v_motive_812_, lean_object* v_t_813_, lean_object* v_h_814_, lean_object* v_assign_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_813_, v_assign_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_binOp_elim___redArg(lean_object* v_t_817_, lean_object* v_binOp_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_817_, v_binOp_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_binOp_elim(lean_object* v_motive_820_, lean_object* v_t_821_, lean_object* v_h_822_, lean_object* v_binOp_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_821_, v_binOp_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_objLit_elim___redArg(lean_object* v_t_825_, lean_object* v_objLit_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_825_, v_objLit_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_objLit_elim(lean_object* v_motive_828_, lean_object* v_t_829_, lean_object* v_h_830_, lean_object* v_objLit_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_829_, v_objLit_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupS_elim___redArg(lean_object* v_t_833_, lean_object* v_lookupS_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_833_, v_lookupS_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupS_elim(lean_object* v_motive_836_, lean_object* v_t_837_, lean_object* v_h_838_, lean_object* v_lookupS_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_837_, v_lookupS_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupD_elim___redArg(lean_object* v_t_841_, lean_object* v_lookupD_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_841_, v_lookupD_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lookupD_elim(lean_object* v_motive_844_, lean_object* v_t_845_, lean_object* v_h_846_, lean_object* v_lookupD_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_845_, v_lookupD_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateS_elim___redArg(lean_object* v_t_849_, lean_object* v_updateS_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_849_, v_updateS_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateS_elim(lean_object* v_motive_852_, lean_object* v_t_853_, lean_object* v_h_854_, lean_object* v_updateS_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_853_, v_updateS_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateD_elim___redArg(lean_object* v_t_857_, lean_object* v_updateD_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_857_, v_updateD_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_updateD_elim(lean_object* v_motive_860_, lean_object* v_t_861_, lean_object* v_h_862_, lean_object* v_updateD_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_861_, v_updateD_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_call_elim___redArg(lean_object* v_t_865_, lean_object* v_call_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_865_, v_call_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_call_elim(lean_object* v_motive_868_, lean_object* v_t_869_, lean_object* v_h_870_, lean_object* v_call_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_869_, v_call_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_seq_elim___redArg(lean_object* v_t_873_, lean_object* v_seq_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_873_, v_seq_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_seq_elim(lean_object* v_motive_876_, lean_object* v_t_877_, lean_object* v_h_878_, lean_object* v_seq_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_877_, v_seq_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ifElse_elim___redArg(lean_object* v_t_881_, lean_object* v_ifElse_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_881_, v_ifElse_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ifElse_elim(lean_object* v_motive_884_, lean_object* v_t_885_, lean_object* v_h_886_, lean_object* v_ifElse_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_885_, v_ifElse_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_whileDo_elim___redArg(lean_object* v_t_889_, lean_object* v_whileDo_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_889_, v_whileDo_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_whileDo_elim(lean_object* v_motive_892_, lean_object* v_t_893_, lean_object* v_h_894_, lean_object* v_whileDo_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_893_, v_whileDo_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ret_elim___redArg(lean_object* v_t_897_, lean_object* v_ret_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_897_, v_ret_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_ret_elim(lean_object* v_motive_900_, lean_object* v_t_901_, lean_object* v_h_902_, lean_object* v_ret_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_901_, v_ret_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setTaint_elim___redArg(lean_object* v_t_905_, lean_object* v_setTaint_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_905_, v_setTaint_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setTaint_elim(lean_object* v_motive_908_, lean_object* v_t_909_, lean_object* v_h_910_, lean_object* v_setTaint_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_909_, v_setTaint_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setSink_elim___redArg(lean_object* v_t_913_, lean_object* v_setSink_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_913_, v_setSink_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_setSink_elim(lean_object* v_motive_916_, lean_object* v_t_917_, lean_object* v_h_918_, lean_object* v_setSink_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = lp_modeljs__proofs_CoreJS_Stmt_ctorElim___redArg(v_t_917_, v_setSink_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3___lam__0(lean_object* v___y_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v___y_921_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5_spec__7(lean_object* v_x_924_, lean_object* v_x_925_, lean_object* v_x_926_){
_start:
{
if (lean_obj_tag(v_x_926_) == 0)
{
lean_dec(v_x_924_);
return v_x_925_;
}
else
{
lean_object* v_head_927_; lean_object* v_tail_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_939_; 
v_head_927_ = lean_ctor_get(v_x_926_, 0);
v_tail_928_ = lean_ctor_get(v_x_926_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_926_);
if (v_isSharedCheck_939_ == 0)
{
v___x_930_ = v_x_926_;
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_tail_928_);
lean_inc(v_head_927_);
lean_dec(v_x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_939_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
lean_inc(v_x_924_);
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 5);
lean_ctor_set(v___x_930_, 1, v_x_924_);
lean_ctor_set(v___x_930_, 0, v_x_925_);
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_x_925_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_x_924_);
v___x_933_ = v_reuseFailAlloc_938_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_head_927_, v___x_934_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_933_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v_x_925_ = v___x_936_;
v_x_926_ = v_tail_928_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5(lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
if (lean_obj_tag(v_x_942_) == 0)
{
lean_dec(v_x_940_);
return v_x_941_;
}
else
{
lean_object* v_head_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_955_; 
v_head_943_ = lean_ctor_get(v_x_942_, 0);
v_tail_944_ = lean_ctor_get(v_x_942_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_x_942_);
if (v_isSharedCheck_955_ == 0)
{
v___x_946_ = v_x_942_;
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_inc(v_head_943_);
lean_dec(v_x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_955_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
lean_inc(v_x_940_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 5);
lean_ctor_set(v___x_946_, 1, v_x_940_);
lean_ctor_set(v___x_946_, 0, v_x_941_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_x_941_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_x_940_);
v___x_949_ = v_reuseFailAlloc_954_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_head_943_, v___x_950_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_949_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5_spec__7(v_x_940_, v___x_952_, v_tail_944_);
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3(lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v___x_958_; 
lean_dec(v_x_957_);
v___x_958_ = lean_box(0);
return v___x_958_;
}
else
{
lean_object* v_tail_959_; 
v_tail_959_ = lean_ctor_get(v_x_956_, 1);
if (lean_obj_tag(v_tail_959_) == 0)
{
lean_object* v_head_960_; lean_object* v___x_961_; 
lean_dec(v_x_957_);
v_head_960_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_head_960_);
lean_dec_ref_known(v_x_956_, 2);
v___x_961_ = lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3___lam__0(v_head_960_);
return v___x_961_;
}
else
{
lean_object* v_head_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc(v_tail_959_);
v_head_962_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_head_962_);
lean_dec_ref_known(v_x_956_, 2);
v___x_963_ = lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3___lam__0(v_head_962_);
v___x_964_ = lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3_spec__5(v_x_957_, v___x_963_, v_tail_959_);
return v___x_964_;
}
}
}
}
static lean_object* _init_lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__2));
v___x_977_ = lean_string_length(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_obj_once(&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7, &lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7_once, _init_lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__7);
v___x_979_ = lean_nat_to_int(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg(lean_object* v_a_984_){
_start:
{
if (lean_obj_tag(v_a_984_) == 0)
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__1));
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v___x_986_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5));
v___x_987_ = lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__1_spec__3(v_a_984_, v___x_986_);
v___x_988_ = lean_obj_once(&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8, &lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8_once, _init_lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8);
v___x_989_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__9));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_987_);
v___x_991_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__10));
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_988_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = 0;
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_994_);
return v___x_995_;
}
}
}
static lean_object* _init_lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__0));
v___x_999_ = lean_string_length(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2, &lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2_once, _init_lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__2);
v___x_1001_ = lean_nat_to_int(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(lean_object* v_x_1006_){
_start:
{
lean_object* v_fst_1007_; lean_object* v_snd_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1032_; 
v_fst_1007_ = lean_ctor_get(v_x_1006_, 0);
v_snd_1008_ = lean_ctor_get(v_x_1006_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_x_1006_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1010_ = v_x_1006_;
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_snd_1008_);
lean_inc(v_fst_1007_);
lean_dec(v_x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1032_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1012_ = l_String_quote(v_fst_1007_);
v___x_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_box(0);
if (v_isShared_1011_ == 0)
{
lean_ctor_set_tag(v___x_1010_, 1);
lean_ctor_set(v___x_1010_, 1, v___x_1014_);
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1016_ = v___x_1010_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_snd_1008_, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_1016_);
v___x_1020_ = l_List_reverse___redArg(v___x_1019_);
v___x_1021_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5));
v___x_1022_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(v___x_1020_, v___x_1021_);
v___x_1023_ = lean_obj_once(&lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3, &lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3_once, _init_lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__3);
v___x_1024_ = ((lean_object*)(lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__4));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1022_);
v___x_1026_ = ((lean_object*)(lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg___closed__5));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = 0;
v___x_1030_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*1, v___x_1029_);
return v___x_1030_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2_spec__4(lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_dec(v_x_1033_);
return v_x_1034_;
}
else
{
lean_object* v_head_1036_; lean_object* v_tail_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1047_; 
v_head_1036_ = lean_ctor_get(v_x_1035_, 0);
v_tail_1037_ = lean_ctor_get(v_x_1035_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1035_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1039_ = v_x_1035_;
v_isShared_1040_ = v_isSharedCheck_1047_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_tail_1037_);
lean_inc(v_head_1036_);
lean_dec(v_x_1035_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1047_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
lean_inc(v_x_1033_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 5);
lean_ctor_set(v___x_1039_, 1, v_x_1033_);
lean_ctor_set(v___x_1039_, 0, v_x_1034_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_x_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_x_1033_);
v___x_1042_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(v_head_1036_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v_x_1034_ = v___x_1044_;
v_x_1035_ = v_tail_1037_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2(lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
lean_dec(v_x_1048_);
return v_x_1049_;
}
else
{
lean_object* v_head_1051_; lean_object* v_tail_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1062_; 
v_head_1051_ = lean_ctor_get(v_x_1050_, 0);
v_tail_1052_ = lean_ctor_get(v_x_1050_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1050_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1054_ = v_x_1050_;
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_tail_1052_);
lean_inc(v_head_1051_);
lean_dec(v_x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
lean_inc(v_x_1048_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set_tag(v___x_1054_, 5);
lean_ctor_set(v___x_1054_, 1, v_x_1048_);
lean_ctor_set(v___x_1054_, 0, v_x_1049_);
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_x_1049_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_x_1048_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(v_head_1051_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lp_modeljs__proofs_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2_spec__4(v_x_1048_, v___x_1059_, v_tail_1052_);
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v___x_1065_; 
lean_dec(v_x_1064_);
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
else
{
lean_object* v_tail_1066_; 
v_tail_1066_ = lean_ctor_get(v_x_1063_, 1);
if (lean_obj_tag(v_tail_1066_) == 0)
{
lean_object* v_head_1067_; lean_object* v___x_1068_; 
lean_dec(v_x_1064_);
v_head_1067_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_head_1067_);
lean_dec_ref_known(v_x_1063_, 2);
v___x_1068_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(v_head_1067_);
return v___x_1068_;
}
else
{
lean_object* v_head_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_inc(v_tail_1066_);
v_head_1069_ = lean_ctor_get(v_x_1063_, 0);
lean_inc(v_head_1069_);
lean_dec_ref_known(v_x_1063_, 2);
v___x_1070_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(v_head_1069_);
v___x_1071_ = lp_modeljs__proofs_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1_spec__2(v_x_1064_, v___x_1070_, v_tail_1066_);
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___redArg(lean_object* v_a_1072_){
_start:
{
if (lean_obj_tag(v_a_1072_) == 0)
{
lean_object* v___x_1073_; 
v___x_1073_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__1));
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; 
v___x_1074_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__5));
v___x_1075_ = lp_modeljs__proofs_Std_Format_joinSep___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__1(v_a_1072_, v___x_1074_);
v___x_1076_ = lean_obj_once(&lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8, &lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8_once, _init_lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__8);
v___x_1077_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__9));
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1075_);
v___x_1079_ = ((lean_object*)(lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg___closed__10));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1076_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = 0;
v___x_1083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
return v___x_1083_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr(lean_object* v_x_1171_, lean_object* v_prec_1172_){
_start:
{
lean_object* v___y_1174_; 
switch(lean_obj_tag(v_x_1171_))
{
case 0:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = lean_unsigned_to_nat(1024u);
v___x_1181_ = lean_nat_dec_le(v___x_1180_, v_prec_1172_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1174_ = v___x_1182_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1174_ = v___x_1183_;
goto v___jp_1173_;
}
}
case 1:
{
lean_object* v_x_1184_; lean_object* v_e_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1210_; 
v_x_1184_ = lean_ctor_get(v_x_1171_, 0);
v_e_1185_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1187_ = v_x_1171_;
v_isShared_1188_ = v_isSharedCheck_1210_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_e_1185_);
lean_inc(v_x_1184_);
lean_dec(v_x_1171_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1210_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___y_1190_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(1024u);
v___x_1207_ = lean_nat_dec_le(v___x_1206_, v_prec_1172_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1190_ = v___x_1208_;
goto v___jp_1189_;
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1190_ = v___x_1209_;
goto v___jp_1189_;
}
v___jp_1189_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1191_ = lean_box(1);
v___x_1192_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__4));
v___x_1193_ = l_String_quote(v_x_1184_);
v___x_1194_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set_tag(v___x_1187_, 5);
lean_ctor_set(v___x_1187_, 1, v___x_1194_);
lean_ctor_set(v___x_1187_, 0, v___x_1192_);
v___x_1196_ = v___x_1187_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1191_);
v___x_1198_ = lean_unsigned_to_nat(1024u);
v___x_1199_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1185_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1197_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
lean_inc(v___y_1190_);
v___x_1201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1190_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = 0;
v___x_1203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*1, v___x_1202_);
v___x_1204_ = l_Repr_addAppParen(v___x_1203_, v_prec_1172_);
return v___x_1204_;
}
}
}
}
case 2:
{
lean_object* v_x_1211_; lean_object* v_00_u03ba_1212_; uint8_t v_op_1213_; lean_object* v_e_u2081_1214_; lean_object* v_e_u2082_1215_; lean_object* v___y_1217_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_x_1211_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_x_1211_);
v_00_u03ba_1212_ = lean_ctor_get(v_x_1171_, 1);
lean_inc(v_00_u03ba_1212_);
v_op_1213_ = lean_ctor_get_uint8(v_x_1171_, sizeof(void*)*4);
v_e_u2081_1214_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_e_u2081_1214_);
v_e_u2082_1215_ = lean_ctor_get(v_x_1171_, 3);
lean_inc_ref(v_e_u2082_1215_);
lean_dec_ref_known(v_x_1171_, 4);
v___x_1241_ = lean_unsigned_to_nat(1024u);
v___x_1242_ = lean_nat_dec_le(v___x_1241_, v_prec_1172_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
v___x_1243_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1217_ = v___x_1243_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1217_ = v___x_1244_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__7));
v___x_1220_ = l_String_quote(v_x_1211_);
v___x_1221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
v___x_1222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
lean_ctor_set(v___x_1223_, 1, v___x_1218_);
v___x_1224_ = l_Nat_reprFast(v_00_u03ba_1212_);
v___x_1225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1223_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v___x_1218_);
v___x_1228_ = lean_unsigned_to_nat(1024u);
v___x_1229_ = lp_modeljs__proofs_CoreJS_instReprBinOp_repr(v_op_1213_, v___x_1228_);
v___x_1230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1227_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v___x_1218_);
v___x_1232_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2081_1214_, v___x_1228_);
v___x_1233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1218_);
v___x_1235_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2082_1215_, v___x_1228_);
v___x_1236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1234_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
lean_inc(v___y_1217_);
v___x_1237_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1217_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = 0;
v___x_1239_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1239_, 0, v___x_1237_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*1, v___x_1238_);
v___x_1240_ = l_Repr_addAppParen(v___x_1239_, v_prec_1172_);
return v___x_1240_;
}
}
case 3:
{
lean_object* v_x_1245_; lean_object* v_00_u03ba_1246_; lean_object* v_fs_1247_; lean_object* v___y_1249_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_x_1245_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_x_1245_);
v_00_u03ba_1246_ = lean_ctor_get(v_x_1171_, 1);
lean_inc(v_00_u03ba_1246_);
v_fs_1247_ = lean_ctor_get(v_x_1171_, 2);
lean_inc(v_fs_1247_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1266_ = lean_unsigned_to_nat(1024u);
v___x_1267_ = lean_nat_dec_le(v___x_1266_, v_prec_1172_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1249_ = v___x_1268_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1249_ = v___x_1269_;
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1250_ = lean_box(1);
v___x_1251_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__10));
v___x_1252_ = l_String_quote(v_x_1245_);
v___x_1253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1251_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1250_);
v___x_1256_ = l_Nat_reprFast(v_00_u03ba_1246_);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1250_);
v___x_1260_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___redArg(v_fs_1247_);
v___x_1261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
lean_inc(v___y_1249_);
v___x_1262_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___y_1249_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = 0;
v___x_1264_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*1, v___x_1263_);
v___x_1265_ = l_Repr_addAppParen(v___x_1264_, v_prec_1172_);
return v___x_1265_;
}
}
case 4:
{
lean_object* v_x_1270_; lean_object* v_e_1271_; lean_object* v_p_1272_; lean_object* v___y_1274_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_x_1270_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_x_1270_);
v_e_1271_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_e_1271_);
v_p_1272_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_p_1272_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1292_ = lean_unsigned_to_nat(1024u);
v___x_1293_ = lean_nat_dec_le(v___x_1292_, v_prec_1172_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1274_ = v___x_1294_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1274_ = v___x_1295_;
goto v___jp_1273_;
}
v___jp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1275_ = lean_box(1);
v___x_1276_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__13));
v___x_1277_ = l_String_quote(v_x_1270_);
v___x_1278_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1276_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v___x_1275_);
v___x_1281_ = lean_unsigned_to_nat(1024u);
v___x_1282_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1271_, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1280_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set(v___x_1284_, 1, v___x_1275_);
v___x_1285_ = l_String_quote(v_p_1272_);
v___x_1286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
v___x_1287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1284_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_inc(v___y_1274_);
v___x_1288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___y_1274_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = 0;
v___x_1290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set_uint8(v___x_1290_, sizeof(void*)*1, v___x_1289_);
v___x_1291_ = l_Repr_addAppParen(v___x_1290_, v_prec_1172_);
return v___x_1291_;
}
}
case 5:
{
lean_object* v_x_1296_; lean_object* v_e_u2081_1297_; lean_object* v_e_u2082_1298_; lean_object* v___y_1300_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_x_1296_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_x_1296_);
v_e_u2081_1297_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_e_u2081_1297_);
v_e_u2082_1298_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_e_u2082_1298_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1317_ = lean_unsigned_to_nat(1024u);
v___x_1318_ = lean_nat_dec_le(v___x_1317_, v_prec_1172_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1300_ = v___x_1319_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1300_ = v___x_1320_;
goto v___jp_1299_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1301_ = lean_box(1);
v___x_1302_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__16));
v___x_1303_ = l_String_quote(v_x_1296_);
v___x_1304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
v___x_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1301_);
v___x_1307_ = lean_unsigned_to_nat(1024u);
v___x_1308_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2081_1297_, v___x_1307_);
v___x_1309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1306_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___x_1301_);
v___x_1311_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2082_1298_, v___x_1307_);
v___x_1312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_inc(v___y_1300_);
v___x_1313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___y_1300_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = 0;
v___x_1315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*1, v___x_1314_);
v___x_1316_ = l_Repr_addAppParen(v___x_1315_, v_prec_1172_);
return v___x_1316_;
}
}
case 6:
{
lean_object* v_e_u2081_1321_; lean_object* v_p_1322_; lean_object* v_e_u2082_1323_; lean_object* v___y_1325_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_e_u2081_1321_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_u2081_1321_);
v_p_1322_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_p_1322_);
v_e_u2082_1323_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_e_u2082_1323_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1342_ = lean_unsigned_to_nat(1024u);
v___x_1343_ = lean_nat_dec_le(v___x_1342_, v_prec_1172_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1325_ = v___x_1344_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1325_ = v___x_1345_;
goto v___jp_1324_;
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1326_ = lean_box(1);
v___x_1327_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__19));
v___x_1328_ = lean_unsigned_to_nat(1024u);
v___x_1329_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2081_1321_, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1327_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1326_);
v___x_1332_ = l_String_quote(v_p_1322_);
v___x_1333_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1331_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1326_);
v___x_1336_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2082_1323_, v___x_1328_);
v___x_1337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
lean_inc(v___y_1325_);
v___x_1338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___y_1325_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = 0;
v___x_1340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1339_);
v___x_1341_ = l_Repr_addAppParen(v___x_1340_, v_prec_1172_);
return v___x_1341_;
}
}
case 7:
{
lean_object* v_e_u2081_1346_; lean_object* v_e_u2082_1347_; lean_object* v_e_u2083_1348_; lean_object* v___y_1350_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v_e_u2081_1346_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_u2081_1346_);
v_e_u2082_1347_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_e_u2082_1347_);
v_e_u2083_1348_ = lean_ctor_get(v_x_1171_, 2);
lean_inc_ref(v_e_u2083_1348_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1366_ = lean_unsigned_to_nat(1024u);
v___x_1367_ = lean_nat_dec_le(v___x_1366_, v_prec_1172_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1350_ = v___x_1368_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1350_ = v___x_1369_;
goto v___jp_1349_;
}
v___jp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1351_ = lean_box(1);
v___x_1352_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__22));
v___x_1353_ = lean_unsigned_to_nat(1024u);
v___x_1354_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2081_1346_, v___x_1353_);
v___x_1355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1352_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
lean_ctor_set(v___x_1356_, 1, v___x_1351_);
v___x_1357_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2082_1347_, v___x_1353_);
v___x_1358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1351_);
v___x_1360_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_u2083_1348_, v___x_1353_);
v___x_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
lean_inc(v___y_1350_);
v___x_1362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1350_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = 0;
v___x_1364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*1, v___x_1363_);
v___x_1365_ = l_Repr_addAppParen(v___x_1364_, v_prec_1172_);
return v___x_1365_;
}
}
case 8:
{
lean_object* v_x_1370_; lean_object* v_e_1371_; lean_object* v_es_1372_; lean_object* v___y_1374_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_x_1370_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_x_1370_);
v_e_1371_ = lean_ctor_get(v_x_1171_, 1);
lean_inc_ref(v_e_1371_);
v_es_1372_ = lean_ctor_get(v_x_1171_, 2);
lean_inc(v_es_1372_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1391_ = lean_unsigned_to_nat(1024u);
v___x_1392_ = lean_nat_dec_le(v___x_1391_, v_prec_1172_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
v___x_1393_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1374_ = v___x_1393_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1374_ = v___x_1394_;
goto v___jp_1373_;
}
v___jp_1373_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1375_ = lean_box(1);
v___x_1376_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__25));
v___x_1377_ = l_String_quote(v_x_1370_);
v___x_1378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
v___x_1379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1376_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1375_);
v___x_1381_ = lean_unsigned_to_nat(1024u);
v___x_1382_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1371_, v___x_1381_);
v___x_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1375_);
v___x_1385_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg(v_es_1372_);
v___x_1386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
lean_inc(v___y_1374_);
v___x_1387_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1387_, 0, v___y_1374_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = 0;
v___x_1389_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*1, v___x_1388_);
v___x_1390_ = l_Repr_addAppParen(v___x_1389_, v_prec_1172_);
return v___x_1390_;
}
}
case 9:
{
lean_object* v_s_u2081_1395_; lean_object* v_s_u2082_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1419_; 
v_s_u2081_1395_ = lean_ctor_get(v_x_1171_, 0);
v_s_u2082_1396_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1398_ = v_x_1171_;
v_isShared_1399_ = v_isSharedCheck_1419_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_s_u2082_1396_);
lean_inc(v_s_u2081_1395_);
lean_dec(v_x_1171_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1419_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___y_1402_; uint8_t v___x_1416_; 
v___x_1400_ = lean_unsigned_to_nat(1024u);
v___x_1416_ = lean_nat_dec_le(v___x_1400_, v_prec_1172_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1402_ = v___x_1417_;
goto v___jp_1401_;
}
else
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1402_ = v___x_1418_;
goto v___jp_1401_;
}
v___jp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1403_ = lean_box(1);
v___x_1404_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__28));
v___x_1405_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_s_u2081_1395_, v___x_1400_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 5);
lean_ctor_set(v___x_1398_, 1, v___x_1405_);
lean_ctor_set(v___x_1398_, 0, v___x_1404_);
v___x_1407_ = v___x_1398_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1408_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v___x_1403_);
v___x_1409_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_s_u2082_1396_, v___x_1400_);
v___x_1410_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
lean_inc(v___y_1402_);
v___x_1411_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___y_1402_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = 0;
v___x_1413_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*1, v___x_1412_);
v___x_1414_ = l_Repr_addAppParen(v___x_1413_, v_prec_1172_);
return v___x_1414_;
}
}
}
}
case 10:
{
lean_object* v_e_1420_; lean_object* v_s_u2081_1421_; lean_object* v_s_u2082_1422_; lean_object* v___x_1423_; lean_object* v___y_1425_; uint8_t v___x_1440_; 
v_e_1420_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_1420_);
v_s_u2081_1421_ = lean_ctor_get(v_x_1171_, 1);
lean_inc(v_s_u2081_1421_);
v_s_u2082_1422_ = lean_ctor_get(v_x_1171_, 2);
lean_inc(v_s_u2082_1422_);
lean_dec_ref_known(v_x_1171_, 3);
v___x_1423_ = lean_unsigned_to_nat(1024u);
v___x_1440_ = lean_nat_dec_le(v___x_1423_, v_prec_1172_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1425_ = v___x_1441_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1425_ = v___x_1442_;
goto v___jp_1424_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1426_ = lean_box(1);
v___x_1427_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__31));
v___x_1428_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1420_, v___x_1423_);
v___x_1429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1426_);
v___x_1431_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_s_u2081_1421_, v___x_1423_);
v___x_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1426_);
v___x_1434_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_s_u2082_1422_, v___x_1423_);
v___x_1435_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc(v___y_1425_);
v___x_1436_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___y_1425_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = 0;
v___x_1438_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*1, v___x_1437_);
v___x_1439_ = l_Repr_addAppParen(v___x_1438_, v_prec_1172_);
return v___x_1439_;
}
}
case 11:
{
lean_object* v_e_1443_; lean_object* v_s_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1467_; 
v_e_1443_ = lean_ctor_get(v_x_1171_, 0);
v_s_1444_ = lean_ctor_get(v_x_1171_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_x_1171_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1446_ = v_x_1171_;
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_s_1444_);
lean_inc(v_e_1443_);
lean_dec(v_x_1171_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1467_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___y_1450_; uint8_t v___x_1464_; 
v___x_1448_ = lean_unsigned_to_nat(1024u);
v___x_1464_ = lean_nat_dec_le(v___x_1448_, v_prec_1172_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1450_ = v___x_1465_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1450_ = v___x_1466_;
goto v___jp_1449_;
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1451_ = lean_box(1);
v___x_1452_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__34));
v___x_1453_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1443_, v___x_1448_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 5);
lean_ctor_set(v___x_1446_, 1, v___x_1453_);
lean_ctor_set(v___x_1446_, 0, v___x_1452_);
v___x_1455_ = v___x_1446_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1451_);
v___x_1457_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_s_1444_, v___x_1448_);
v___x_1458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_inc(v___y_1450_);
v___x_1459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___y_1450_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = 0;
v___x_1461_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*1, v___x_1460_);
v___x_1462_ = l_Repr_addAppParen(v___x_1461_, v_prec_1172_);
return v___x_1462_;
}
}
}
}
case 12:
{
lean_object* v_e_1468_; lean_object* v___y_1470_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_e_1468_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_1468_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1479_ = lean_unsigned_to_nat(1024u);
v___x_1480_ = lean_nat_dec_le(v___x_1479_, v_prec_1172_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1470_ = v___x_1481_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1470_ = v___x_1482_;
goto v___jp_1469_;
}
v___jp_1469_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1471_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__37));
v___x_1472_ = lean_unsigned_to_nat(1024u);
v___x_1473_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1468_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1471_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
lean_inc(v___y_1470_);
v___x_1475_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1470_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = 0;
v___x_1477_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1477_, 0, v___x_1475_);
lean_ctor_set_uint8(v___x_1477_, sizeof(void*)*1, v___x_1476_);
v___x_1478_ = l_Repr_addAppParen(v___x_1477_, v_prec_1172_);
return v___x_1478_;
}
}
case 13:
{
lean_object* v_e_1483_; lean_object* v___y_1485_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_e_1483_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_1483_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1494_ = lean_unsigned_to_nat(1024u);
v___x_1495_ = lean_nat_dec_le(v___x_1494_, v_prec_1172_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1485_ = v___x_1496_;
goto v___jp_1484_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1485_ = v___x_1497_;
goto v___jp_1484_;
}
v___jp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1486_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__40));
v___x_1487_ = lean_unsigned_to_nat(1024u);
v___x_1488_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1483_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1486_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
lean_inc(v___y_1485_);
v___x_1490_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1490_, 0, v___y_1485_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
v___x_1491_ = 0;
v___x_1492_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*1, v___x_1491_);
v___x_1493_ = l_Repr_addAppParen(v___x_1492_, v_prec_1172_);
return v___x_1493_;
}
}
default: 
{
lean_object* v_e_1498_; lean_object* v___y_1500_; lean_object* v___x_1509_; uint8_t v___x_1510_; 
v_e_1498_ = lean_ctor_get(v_x_1171_, 0);
lean_inc_ref(v_e_1498_);
lean_dec_ref_known(v_x_1171_, 1);
v___x_1509_ = lean_unsigned_to_nat(1024u);
v___x_1510_ = lean_nat_dec_le(v___x_1509_, v_prec_1172_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__4);
v___y_1500_ = v___x_1511_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_obj_once(&lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5, &lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5_once, _init_lp_modeljs__proofs_CoreJS_instReprVal_repr___closed__5);
v___y_1500_ = v___x_1512_;
goto v___jp_1499_;
}
v___jp_1499_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1501_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__43));
v___x_1502_ = lean_unsigned_to_nat(1024u);
v___x_1503_ = lp_modeljs__proofs_CoreJS_instReprExpr_repr(v_e_1498_, v___x_1502_);
v___x_1504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1501_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
lean_inc(v___y_1500_);
v___x_1505_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___y_1500_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = 0;
v___x_1507_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*1, v___x_1506_);
v___x_1508_ = l_Repr_addAppParen(v___x_1507_, v_prec_1172_);
return v___x_1508_;
}
}
}
v___jp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1175_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_instReprStmt_repr___closed__1));
lean_inc(v___y_1174_);
v___x_1176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = 0;
v___x_1178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*1, v___x_1177_);
v___x_1179_ = l_Repr_addAppParen(v___x_1178_, v_prec_1172_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_instReprStmt_repr___boxed(lean_object* v_x_1513_, lean_object* v_prec_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = lp_modeljs__proofs_CoreJS_instReprStmt_repr(v_x_1513_, v_prec_1514_);
lean_dec(v_prec_1514_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0(lean_object* v_a_1516_, lean_object* v_n_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___redArg(v_a_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0___boxed(lean_object* v_a_1519_, lean_object* v_n_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__0(v_a_1519_, v_n_1520_);
lean_dec(v_n_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1(lean_object* v_a_1522_, lean_object* v_n_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___redArg(v_a_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1___boxed(lean_object* v_a_1525_, lean_object* v_n_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = lp_modeljs__proofs_List_repr___at___00CoreJS_instReprStmt_repr_spec__1(v_a_1525_, v_n_1526_);
lean_dec(v_n_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0(lean_object* v_x_1528_, lean_object* v_x_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___redArg(v_x_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0___boxed(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = lp_modeljs__proofs_Prod_repr___at___00List_repr___at___00CoreJS_instReprStmt_repr_spec__0_spec__0(v_x_1531_, v_x_1532_);
lean_dec(v_x_1532_);
return v_res_1533_;
}
}
static lean_object* _init_lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__5));
v___x_1574_ = l_String_toRawSubstring_x27(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1(lean_object* v_x_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2));
lean_inc(v_x_1598_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_x_1598_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_x_1598_);
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1600_);
return v___x_1604_;
}
else
{
lean_object* v_quotContext_1605_; lean_object* v_currMacroScope_1606_; lean_object* v_ref_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_quotContext_1605_ = lean_ctor_get(v_a_1599_, 1);
v_currMacroScope_1606_ = lean_ctor_get(v_a_1599_, 2);
v_ref_1607_ = lean_ctor_get(v_a_1599_, 5);
v___x_1608_ = lean_unsigned_to_nat(0u);
v___x_1609_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(2u);
v___x_1611_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1610_);
lean_dec(v_x_1598_);
v___x_1612_ = 0;
v___x_1613_ = l_Lean_SourceInfo_fromRef(v_ref_1607_, v___x_1612_);
v___x_1614_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4));
v___x_1615_ = lean_obj_once(&lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6, &lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6_once, _init_lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__6);
v___x_1616_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__9));
lean_inc(v_currMacroScope_1606_);
lean_inc(v_quotContext_1605_);
v___x_1617_ = l_Lean_addMacroScope(v_quotContext_1605_, v___x_1616_, v_currMacroScope_1606_);
v___x_1618_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__14));
lean_inc_n(v___x_1613_, 2);
v___x_1619_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1613_);
lean_ctor_set(v___x_1619_, 1, v___x_1615_);
lean_ctor_set(v___x_1619_, 2, v___x_1617_);
lean_ctor_set(v___x_1619_, 3, v___x_1618_);
v___x_1620_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__16));
v___x_1621_ = l_Lean_Syntax_node2(v___x_1613_, v___x_1620_, v___x_1609_, v___x_1611_);
v___x_1622_ = l_Lean_Syntax_node2(v___x_1613_, v___x_1614_, v___x_1619_, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
lean_ctor_set(v___x_1623_, 1, v_a_1600_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___boxed(lean_object* v_x_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1(v_x_1624_, v_a_1625_, v_a_1626_);
lean_dec_ref(v_a_1625_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1(lean_object* v_x_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______macroRules__CoreJS__term___x3b_x3b____1___closed__4));
lean_inc(v_x_1631_);
v___x_1635_ = l_Lean_Syntax_isOfKind(v_x_1631_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_x_1631_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v_a_1633_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = l_Lean_Syntax_getArg(v_x_1631_, v___x_1638_);
v___x_1640_ = ((lean_object*)(lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___closed__1));
lean_inc(v___x_1639_);
v___x_1641_ = l_Lean_Syntax_isOfKind(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec(v___x_1639_);
lean_dec(v_x_1631_);
v___x_1642_ = lean_box(0);
v___x_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1633_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1644_ = lean_unsigned_to_nat(1u);
v___x_1645_ = l_Lean_Syntax_getArg(v_x_1631_, v___x_1644_);
lean_dec(v_x_1631_);
v___x_1646_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1645_);
v___x_1647_ = l_Lean_Syntax_matchesNull(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v___x_1645_);
lean_dec(v___x_1639_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1633_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v_ref_1652_; uint8_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1650_ = l_Lean_Syntax_getArg(v___x_1645_, v___x_1638_);
v___x_1651_ = l_Lean_Syntax_getArg(v___x_1645_, v___x_1644_);
lean_dec(v___x_1645_);
v_ref_1652_ = l_Lean_replaceRef(v___x_1639_, v_a_1632_);
lean_dec(v___x_1639_);
v___x_1653_ = 0;
v___x_1654_ = l_Lean_SourceInfo_fromRef(v_ref_1652_, v___x_1653_);
lean_dec(v_ref_1652_);
v___x_1655_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__2));
v___x_1656_ = ((lean_object*)(lp_modeljs__proofs_CoreJS_term___x3b_x3b___00__closed__5));
lean_inc(v___x_1654_);
v___x_1657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1654_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_Syntax_node3(v___x_1654_, v___x_1655_, v___x_1650_, v___x_1657_, v___x_1651_);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_a_1633_);
return v___x_1659_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1___boxed(lean_object* v_x_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = lp_modeljs__proofs_CoreJS___aux__CoreJsSyntax______unexpand__CoreJS__Stmt__seq__1(v_x_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_lits(lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_object* v_v_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_v_1665_ = lean_ctor_get(v_x_1664_, 0);
v___x_1666_ = lean_box(0);
lean_inc_ref(v_v_1665_);
v___x_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1667_, 0, v_v_1665_);
lean_ctor_set(v___x_1667_, 1, v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_box(0);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Expr_lits___boxed(lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_x_1669_);
lean_dec_ref(v_x_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0(lean_object* v_as_1671_, size_t v_i_1672_, size_t v_stop_1673_, lean_object* v_b_1674_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_eq(v_i_1672_, v_stop_1673_);
if (v___x_1675_ == 0)
{
size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1676_ = ((size_t)1ULL);
v___x_1677_ = lean_usize_sub(v_i_1672_, v___x_1676_);
v___x_1678_ = lean_array_uget_borrowed(v_as_1671_, v___x_1677_);
v___x_1679_ = lp_modeljs__proofs_CoreJS_Expr_lits(v___x_1678_);
v___x_1680_ = l_List_appendTR___redArg(v___x_1679_, v_b_1674_);
v_i_1672_ = v___x_1677_;
v_b_1674_ = v___x_1680_;
goto _start;
}
else
{
return v_b_1674_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0___boxed(lean_object* v_as_1682_, lean_object* v_i_1683_, lean_object* v_stop_1684_, lean_object* v_b_1685_){
_start:
{
size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1684_);
lean_dec(v_stop_1684_);
v_res_1688_ = lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0(v_as_1682_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1685_);
lean_dec_ref(v_as_1682_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0(lean_object* v_init_1689_, lean_object* v_l_1690_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1691_ = lean_array_mk(v_l_1690_);
v___x_1692_ = lean_array_get_size(v___x_1691_);
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_nat_dec_lt(v___x_1693_, v___x_1692_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v___x_1691_);
return v_init_1689_;
}
else
{
size_t v___x_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_usize_of_nat(v___x_1692_);
v___x_1696_ = ((size_t)0ULL);
v___x_1697_ = lp_modeljs__proofs___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0_spec__0(v___x_1691_, v___x_1695_, v___x_1696_, v_init_1689_);
lean_dec_ref(v___x_1691_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs___private_CoreJsSyntax_0__CoreJS_litsOfExprs(lean_object* v_es_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_box(0);
v___x_1700_ = lp_modeljs__proofs_List_foldrTR___at___00__private_CoreJsSyntax_0__CoreJS_litsOfExprs_spec__0(v___x_1699_, v_es_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_List_mapTR_loop___at___00CoreJS_Stmt_lits_spec__0(lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
if (lean_obj_tag(v_a_1701_) == 0)
{
lean_object* v___x_1703_; 
v___x_1703_ = l_List_reverse___redArg(v_a_1702_);
return v___x_1703_;
}
else
{
lean_object* v_head_1704_; lean_object* v_tail_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1714_; 
v_head_1704_ = lean_ctor_get(v_a_1701_, 0);
v_tail_1705_ = lean_ctor_get(v_a_1701_, 1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_a_1701_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1707_ = v_a_1701_;
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_tail_1705_);
lean_inc(v_head_1704_);
lean_dec(v_a_1701_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1714_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_snd_1709_; lean_object* v___x_1711_; 
v_snd_1709_ = lean_ctor_get(v_head_1704_, 1);
lean_inc(v_snd_1709_);
lean_dec(v_head_1704_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v_a_1702_);
lean_ctor_set(v___x_1707_, 0, v_snd_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_snd_1709_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_a_1702_);
v___x_1711_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v_a_1701_ = v_tail_1705_;
v_a_1702_ = v___x_1711_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_modeljs__proofs_CoreJS_Stmt_lits(lean_object* v_x_1715_){
_start:
{
switch(lean_obj_tag(v_x_1715_))
{
case 0:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
case 1:
{
lean_object* v_e_1717_; lean_object* v___x_1718_; 
v_e_1717_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_e_1717_);
lean_dec_ref_known(v_x_1715_, 2);
v___x_1718_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1717_);
lean_dec_ref(v_e_1717_);
return v___x_1718_;
}
case 2:
{
lean_object* v_e_u2081_1719_; lean_object* v_e_u2082_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_e_u2081_1719_ = lean_ctor_get(v_x_1715_, 2);
lean_inc_ref(v_e_u2081_1719_);
v_e_u2082_1720_ = lean_ctor_get(v_x_1715_, 3);
lean_inc_ref(v_e_u2082_1720_);
lean_dec_ref_known(v_x_1715_, 4);
v___x_1721_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2081_1719_);
lean_dec_ref(v_e_u2081_1719_);
v___x_1722_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2082_1720_);
lean_dec_ref(v_e_u2082_1720_);
v___x_1723_ = l_List_appendTR___redArg(v___x_1721_, v___x_1722_);
return v___x_1723_;
}
case 3:
{
lean_object* v_fs_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_fs_1724_ = lean_ctor_get(v_x_1715_, 2);
lean_inc(v_fs_1724_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1725_ = lean_box(0);
v___x_1726_ = lp_modeljs__proofs_List_mapTR_loop___at___00CoreJS_Stmt_lits_spec__0(v_fs_1724_, v___x_1725_);
v___x_1727_ = lp_modeljs__proofs___private_CoreJsSyntax_0__CoreJS_litsOfExprs(v___x_1726_);
return v___x_1727_;
}
case 4:
{
lean_object* v_e_1728_; lean_object* v_p_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_e_1728_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_e_1728_);
v_p_1729_ = lean_ctor_get(v_x_1715_, 2);
lean_inc_ref(v_p_1729_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_p_1729_);
v___x_1731_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1728_);
lean_dec_ref(v_e_1728_);
v___x_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1730_);
lean_ctor_set(v___x_1732_, 1, v___x_1731_);
return v___x_1732_;
}
case 5:
{
lean_object* v_e_u2081_1733_; lean_object* v_e_u2082_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_e_u2081_1733_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_e_u2081_1733_);
v_e_u2082_1734_ = lean_ctor_get(v_x_1715_, 2);
lean_inc_ref(v_e_u2082_1734_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1735_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2081_1733_);
lean_dec_ref(v_e_u2081_1733_);
v___x_1736_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2082_1734_);
lean_dec_ref(v_e_u2082_1734_);
v___x_1737_ = l_List_appendTR___redArg(v___x_1735_, v___x_1736_);
return v___x_1737_;
}
case 6:
{
lean_object* v_e_u2081_1738_; lean_object* v_p_1739_; lean_object* v_e_u2082_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_e_u2081_1738_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_e_u2081_1738_);
v_p_1739_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_p_1739_);
v_e_u2082_1740_ = lean_ctor_get(v_x_1715_, 2);
lean_inc_ref(v_e_u2082_1740_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_p_1739_);
v___x_1742_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2081_1738_);
lean_dec_ref(v_e_u2081_1738_);
v___x_1743_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2082_1740_);
lean_dec_ref(v_e_u2082_1740_);
v___x_1744_ = l_List_appendTR___redArg(v___x_1742_, v___x_1743_);
v___x_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1741_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
return v___x_1745_;
}
case 7:
{
lean_object* v_e_u2081_1746_; lean_object* v_e_u2082_1747_; lean_object* v_e_u2083_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_e_u2081_1746_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_e_u2081_1746_);
v_e_u2082_1747_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_e_u2082_1747_);
v_e_u2083_1748_ = lean_ctor_get(v_x_1715_, 2);
lean_inc_ref(v_e_u2083_1748_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1749_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2081_1746_);
lean_dec_ref(v_e_u2081_1746_);
v___x_1750_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2082_1747_);
lean_dec_ref(v_e_u2082_1747_);
v___x_1751_ = l_List_appendTR___redArg(v___x_1749_, v___x_1750_);
v___x_1752_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_u2083_1748_);
lean_dec_ref(v_e_u2083_1748_);
v___x_1753_ = l_List_appendTR___redArg(v___x_1751_, v___x_1752_);
return v___x_1753_;
}
case 8:
{
lean_object* v_e_1754_; lean_object* v_es_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_e_1754_ = lean_ctor_get(v_x_1715_, 1);
lean_inc_ref(v_e_1754_);
v_es_1755_ = lean_ctor_get(v_x_1715_, 2);
lean_inc(v_es_1755_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1756_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1754_);
lean_dec_ref(v_e_1754_);
v___x_1757_ = lp_modeljs__proofs___private_CoreJsSyntax_0__CoreJS_litsOfExprs(v_es_1755_);
v___x_1758_ = l_List_appendTR___redArg(v___x_1756_, v___x_1757_);
return v___x_1758_;
}
case 9:
{
lean_object* v_s_u2081_1759_; lean_object* v_s_u2082_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v_s_u2081_1759_ = lean_ctor_get(v_x_1715_, 0);
lean_inc(v_s_u2081_1759_);
v_s_u2082_1760_ = lean_ctor_get(v_x_1715_, 1);
lean_inc(v_s_u2082_1760_);
lean_dec_ref_known(v_x_1715_, 2);
v___x_1761_ = lp_modeljs__proofs_CoreJS_Stmt_lits(v_s_u2081_1759_);
v___x_1762_ = lp_modeljs__proofs_CoreJS_Stmt_lits(v_s_u2082_1760_);
v___x_1763_ = l_List_appendTR___redArg(v___x_1761_, v___x_1762_);
return v___x_1763_;
}
case 10:
{
lean_object* v_e_1764_; lean_object* v_s_u2081_1765_; lean_object* v_s_u2082_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_e_1764_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_e_1764_);
v_s_u2081_1765_ = lean_ctor_get(v_x_1715_, 1);
lean_inc(v_s_u2081_1765_);
v_s_u2082_1766_ = lean_ctor_get(v_x_1715_, 2);
lean_inc(v_s_u2082_1766_);
lean_dec_ref_known(v_x_1715_, 3);
v___x_1767_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1764_);
lean_dec_ref(v_e_1764_);
v___x_1768_ = lp_modeljs__proofs_CoreJS_Stmt_lits(v_s_u2081_1765_);
v___x_1769_ = l_List_appendTR___redArg(v___x_1767_, v___x_1768_);
v___x_1770_ = lp_modeljs__proofs_CoreJS_Stmt_lits(v_s_u2082_1766_);
v___x_1771_ = l_List_appendTR___redArg(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
case 11:
{
lean_object* v_e_1772_; lean_object* v_s_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v_e_1772_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_e_1772_);
v_s_1773_ = lean_ctor_get(v_x_1715_, 1);
lean_inc(v_s_1773_);
lean_dec_ref_known(v_x_1715_, 2);
v___x_1774_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1772_);
lean_dec_ref(v_e_1772_);
v___x_1775_ = lp_modeljs__proofs_CoreJS_Stmt_lits(v_s_1773_);
v___x_1776_ = l_List_appendTR___redArg(v___x_1774_, v___x_1775_);
return v___x_1776_;
}
default: 
{
lean_object* v_e_1777_; lean_object* v___x_1778_; 
v_e_1777_ = lean_ctor_get(v_x_1715_, 0);
lean_inc_ref(v_e_1777_);
lean_dec(v_x_1715_);
v___x_1778_ = lp_modeljs__proofs_CoreJS_Expr_lits(v_e_1777_);
lean_dec_ref(v_e_1777_);
return v___x_1778_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_modeljs__proofs_CoreJsSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_modeljs__proofs_CoreJS_instInhabitedVal_default = _init_lp_modeljs__proofs_CoreJS_instInhabitedVal_default();
lean_mark_persistent(lp_modeljs__proofs_CoreJS_instInhabitedVal_default);
lp_modeljs__proofs_CoreJS_instInhabitedVal = _init_lp_modeljs__proofs_CoreJS_instInhabitedVal();
lean_mark_persistent(lp_modeljs__proofs_CoreJS_instInhabitedVal);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
