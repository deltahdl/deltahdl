#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/const_eval.h"
#include "lexer/token.h"

namespace delta {

struct RtlirParamDecl;

struct ConstVal {
  int64_t value;
  uint32_t width;
  bool is_signed;
  // §5.7.1 (printed page 77) sizes a based literal by its size constant, and
  // §6.20.2 (printed 126) gives a parameter its declared range, so a constant
  // can hold more bits than `value` does. Word i here holds bits 64*(i+2)-1
  // down to 64*(i+1); `value` holds bits 63 down to 0 as before. Empty for a
  // value with no set bit at or above 64, whatever its width, so every reader
  // that consults `value` alone reads what it always read. Filled by
  // ConstEvalLiteral for a literal past 64 bits and by ConstEvalIdentifierFull
  // for a parameter declared past them, and read through const_eval_wide.cpp
  // by a select, a shift, a bitwise, an additive, a multiplicative, a
  // comparison, a logical and a unary operator, a cast, a concatenation and
  // a replication.
  std::vector<uint64_t> high_words = {};
};

// The value `width` and `is_signed` make of `value`: the bits above the width
// are not part of the value, and the top bit of a signed value is its sign. The
// same bit pattern therefore stands for two different numbers according to the
// signedness, which is the difference §11.7's `$signed` and `$unsigned` exist
// to set. Defined in const_eval.cpp.
ConstVal NormalizeConstVal(int64_t value, uint32_t width, bool is_signed);

// §11.6.1 (printed pages 299-300) with §11.8.2 (printed 302-303): what the
// expression an operand stands in has settled for it before it is folded.
// `width` is the size propagated down to a context-determined operand -- an
// operand of an arithmetic or a bitwise operator, the left operand of a
// shift or a power, an arm of a conditional, the expression a cast converts
// (§6.24.1, printed 139), the right-hand side of an assignment to a target
// of a declared width -- and 0 where the operand is self-determined: a
// shift's count, a power's exponent, an element of a concatenation, a
// condition, an argument, the operands of a logical operator, and the value
// of a parameter declared with neither type nor range (§6.20.2, printed
// 126-127). `read_unsigned` says the expression is unsigned, which §11.8.1
// (printed 302) makes it where any operand that is not self-determined is
// unsigned, so a signed operand under it is the unsigned number its bits
// make and is zero-extended rather than sign-extended (§11.8.2's last step,
// printed 303). A default-constructed context is a self-determined operand's.
struct FoldContext {
  uint32_t width = 0;
  bool read_unsigned = false;
};

// The value of `expr` against `scope` as the operand `ctx` describes: folded
// at the size and type the context propagates and read as ReadInContext reads
// it, so the answer is at least ctx.width wide. The two-argument forms fold a
// self-determined expression.
std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope,
                                      FoldContext ctx);
std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                            const ScopeMap& scope,
                                            FoldContext ctx);
std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                           const ScopeMap& scope,
                                           FoldContext ctx);
std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope);
std::optional<ConstVal> ConstEvalLiteral(const Expr* expr);
std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr);

// §11.6.1's Table 11-21 (printed page 300): the value of the conditional
// `expr`, the condition folded self-determined and the arm it selects folded
// in `ctx`, which reaches the arm as it reaches an operand of an arithmetic
// operator. The other arm is not folded: §13.4.3's constant functions
// recurse through the arm a condition does not select, and folding it would
// follow that recursion to the depth cap on every call. Defined in
// const_eval_context.cpp.
std::optional<ConstVal> ConstEvalTernaryFull(const Expr* expr,
                                             const ScopeMap& scope,
                                             FoldContext ctx);

// §6.24.1 (printed page 139): the value of the cast `expr` -- a signing, a
// const, a size or a type cast -- its operand folded as the right-hand side
// of an assignment to a target of the cast's width and cut to it. Defined in
// const_eval_context.cpp.
std::optional<ConstVal> ConstEvalCastFull(const Expr* expr,
                                          const ScopeMap& scope);

// §11.8.2 (printed pages 302-303): `v` as the context `ctx` reads it --
// extended to ctx.width where it is narrower, from its sign where it is
// signed and the context does not read unsigned and with zeros otherwise,
// and unsigned where the context reads unsigned; unchanged where it is as
// wide and of a type the context admits, and always where the context is a
// self-determined operand's. Defined in const_eval_context.cpp.
ConstVal ReadInContext(const ConstVal& v, FoldContext ctx);

// The two operands of a binary expression once each is folded in the context
// §11.8.2 gives it.
struct BinaryOperands {
  ConstVal lhs;
  ConstVal rhs;
};

// §11.6.1's Table 11-21 with §11.8.2: the operands of the binary expression
// `expr` folded against `scope` under `ctx`. An operand of an arithmetic or
// a bitwise operator and the left operand of a shift or a power take the
// context; a shift's count and a power's exponent, the operands of a logical
// operator and those of a relational or an equality operator, which are
// sized to each other alone, are self-determined. The two operands of an
// arithmetic, a bitwise, a relational or an equality operator are then
// brought to one width, the wider, and one type, unsigned where either is
// (§11.8.1): the one that folded narrower, or signed where the other is
// unsigned, is folded again in that shared context, since an operand that is
// itself an expression applied its operator at the width and type it had
// then and the sum, the product or the shift inside it would keep the bits
// that width cut. Empty where an operand does not fold. Defined in
// const_eval_context.cpp.
std::optional<BinaryOperands> FoldBinaryOperands(const Expr* expr,
                                                 const ScopeMap& scope,
                                                 FoldContext ctx);

// §11.6.1's Table 11-21 (printed pages 299-300): whether the binary
// operator `op` answers one bit whatever the width of its operands -- a
// relational, an equality, a logical operator or an implication. Defined in
// const_eval_context.cpp.
bool AnswersOneBit(TokenKind op);

// §6.20.2 (printed pages 126-127) with §11.6.1 (printed 299): the context the
// declaration of `pd` gives the value assigned to it -- the declared width
// where the declaration fixes one, by a range or by a type that is not
// implicit, and a self-determined operand's where the parameter takes its
// range from the value. Never read unsigned: §11.8.1 (printed 302) has the
// type of the right-hand side depend on its operands and not on the target.
// Defined in const_eval_bits.cpp.
FoldContext DeclaredFoldContext(const RtlirParamDecl& pd);

// §6.20.2 with §11.6.1 and §11.8.3 (printed page 303): the value `expr` folded
// against `scope` gives the parameter `pd`: folded in DeclaredFoldContext(pd),
// and cut to the declared width where there is one -- the bits above it
// dropped, and the number read by the expression's own signedness, as
// CastConstVal reads it -- so that `localparam [7:0] V = 16'h1234 + 0` holds
// 0x34. Empty where the expression does not fold. Defined in
// const_eval_bits.cpp.
std::optional<int64_t> FoldParamValue(const RtlirParamDecl& pd,
                                      const Expr* expr, const ScopeMap& scope);
std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                        const ScopeMap& scope);

// §11.4.12: the value of a concatenation, each element's own width of bits
// joined with the first element the most significant, and of a replication,
// the concatenation of its elements repeated the multiplier's number of times
// (§11.4.12.1), each as wide as the sum of its parts and carrying every word
// of them. Empty where an element or the multiplier does not fold, where the
// multiplier is negative, and where the whole would be wider than a fold is
// let grow. Defined in const_eval_wide.cpp.
std::optional<ConstVal> ConstEvalConcatFull(const Expr* expr,
                                            const ScopeMap& scope);
std::optional<ConstVal> ConstEvalReplicateFull(const Expr* expr,
                                               const ScopeMap& scope);

std::optional<ConstVal> ConstEvalSelectFull(const Expr* expr,
                                            const ScopeMap& scope);

// §5.7.1: the bits from 64 up of an integer literal's digits, as
// ConstVal::high_words lays them out, cut to `width`. Empty for a literal no
// wider than 64 bits, for one whose digits set no bit at or above 64, and
// from the first x, z or ? digit on, where the fold ends as ParseIntText's
// does. Defined in const_eval_wide.cpp.
std::vector<uint64_t> LiteralHighWords(std::string_view text, uint32_t width);

// The bit `offset` above the least significant end of `v`, read through
// ConstVal::high_words past bit 63, and 0 for an offset outside the value.
// Defined in const_eval_wide.cpp.
bool ConstValBit(const ConstVal& v, int64_t offset);

// The 64 bits of `v` from bit `lo` upward: bit `lo` of the value lands at bit
// 0 of the answer. A bit below 0 or above the value's top reads 0, so a
// negative `lo` shifts the value up by -lo. Defined in const_eval_wide.cpp.
uint64_t ConstValWindow(const ConstVal& v, int64_t lo);

// §11.6.1's Table 11-21 (printed pages 299-300): whether the binary operator
// `op` sizes its result by its left operand alone, the right being
// self-determined -- the four shifts, their compound assignment forms and
// the power -- rather than by the wider of the two. Defined in
// const_eval.cpp; BitLengthRuleOf in const_eval_bits.cpp holds the same
// rows of the table for $bits.
bool SizedByLeftOperand(TokenKind op);

// §11.8.1 (printed page 302): the signedness of the value the binary operator
// `op` makes of `lhs` and `rhs` -- the left operand's where the right is
// self-determined, and signed where both are otherwise. Defined in
// const_eval.cpp.
bool BinaryResultSigned(TokenKind op, const ConstVal& lhs, const ConstVal& rhs);

// §11.4.10 with §11.4.8, §11.4.3, §11.4.4, §11.4.5 and §11.4.7: a shift, a
// bitwise operator, an arithmetic operator, a relational, an equality or a
// logical operator applied across every word of `lhs` and `rhs`, at width
// `width` -- the result's, which ConstEvalBinaryFull sizes -- for an
// operand that carries bits past 63, and for every shift and power whatever
// their width, whose right operand is read across all of its words; a
// comparison and a logical operator answer one bit. Empty for any other
// operator -- the case equality and wildcard operators -- which the 64-bit
// fold answers on the low word, and for a quotient or a remainder by zero
// and a power §11.4.3 makes x. Defined in const_eval_wide.cpp.
std::optional<ConstVal> EvalWideBinary(TokenKind op, const ConstVal& lhs,
                                       const ConstVal& rhs, uint32_t width);

// §11.4.3 (printed pages 275-276) with §11.4.3.1: the product, the quotient,
// the remainder or the power of `lhs` and `rhs` at width `width`, worked
// across every word of them -- the quotient truncated toward zero, the
// remainder with the sign of the first operand, the power by Table 11-4
// with the exponent read across every word of `rhs` -- and cut to the width
// as §11.6.1 cuts an arithmetic result, which is the wider operand's for
// the first three and the base's for the power. Empty for a divisor of zero
// and for a base of zero under a negative exponent, which the clause makes
// x, as the 64-bit fold answers them. `op` is one of the four; 994404a79
// folded each on the low word. Defined in const_eval_wide_arith.cpp.
std::optional<ConstVal> EvalWideMultiplicative(TokenKind op,
                                               const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width);

// The words of `v` at `width` as an operand of a binary operator or a cast
// reads them: cut to v's own width, and the bits from there up to `width`
// filled from v's sign bit where `sign_extend` asks, which is what §11.4.3.1
// (printed 277), §11.4.4, §11.4.5 and §11.4.8 do to the narrower of two
// signed operands and §6.24.1 to a value cast to a larger size. Word i holds
// bits 64*i+63 down to 64*i, and there are enough words for `width` bits.
// Defined in const_eval_wide.cpp.
std::vector<uint64_t> ExtendedWords(const ConstVal& v, uint32_t width,
                                    bool sign_extend);

// The ConstVal `words`, laid out as ExtendedWords lays them, make at `width`
// and `is_signed`: the first word read as NormalizeConstVal reads a value of
// 64 bits or less, and the rest cut to the width and trimmed to
// ConstVal::high_words' layout. Defined in const_eval_wide.cpp.
ConstVal ConstValOfWords(const std::vector<uint64_t>& words, uint32_t width,
                         bool is_signed);

// `addend` added into `acc` word by word, both of one length, each word's
// carry going into the next and the carry out of the top word dropped.
// Defined in const_eval_wide.cpp.
void AddWords(std::vector<uint64_t>& acc, const std::vector<uint64_t>& addend);

// §11.4.3 (printed 277): the two's complement of `words` across every bit of
// every word, which is what unary minus makes of its operand. Defined in
// const_eval_wide.cpp.
void NegateWords(std::vector<uint64_t>& words);

// The bits of `words` at or above `width` cleared, so that a value read at a
// width contributes nothing above it. Defined in const_eval_wide.cpp.
void ClearBitsFrom(std::vector<uint64_t>& words, uint32_t width);

// The words a value held as 32-bit halves, least significant first, makes.
// Defined in const_eval_wide.cpp.
std::vector<uint64_t> WordsOfHalves(const std::vector<uint32_t>& halves);

// §11.4.3 with §11.4.8 and §11.4.7: unary plus, minus, bitwise negation and
// logical negation applied across every word of `operand`, whose width is
// past 64. Empty for any other operator. Defined in const_eval_wide.cpp.
std::optional<ConstVal> EvalWideUnary(TokenKind op, const ConstVal& operand);

// §11.4.7: whether any bit of `v` is set, read across every word of it, which
// is what a logical operator asks of an operand. Defined in
// const_eval_wide.cpp.
bool ConstValIsNonZero(const ConstVal& v);

// §6.24.1 with §11.7: `v` read at `width` bits and the signedness `is_signed`,
// the words above the width cut away and a wider width padded from v's own
// sign where v is signed and with zeros otherwise. NormalizeConstVal's answer
// for a width of 64 or less, and one carrying the words above bit 63 for a
// wider one. Defined in const_eval_wide.cpp.
ConstVal CastConstVal(const ConstVal& v, uint32_t width, bool is_signed);

// The parameter of the registered module that `name` names where the
// expression being folded stands, or null when no module is registered, when
// it declares no such parameter, or when the one it declares belongs to a
// generate block the expression does not stand in (§23.9). Defined in
// const_eval.cpp.
const RtlirParamDecl* RegisteredParamNamed(std::string_view name);

// The parameters of the registered module as a scope, for a fold of one of
// their own expressions. Defined in const_eval.cpp.
ScopeMap RegisteredModuleScope();

// §5.7.1: the width an integer literal's size constant states, and 32 for an
// unsized one. Defined in const_eval.cpp.
uint32_t ConstLiteralWidth(const Expr* expr);

// §20.6.2: the value of a `$bits(...)` call whose argument is sized at
// elaboration, or empty. Defined in const_eval_bits.cpp.
std::optional<int64_t> EvalConstBits(const Expr* expr, const ScopeMap& scope);

// §6.20.2: what the name of a value parameter of the registered module is
// worth when the ScopeMap holds `value` for it -- the value read at the
// parameter's declared width and signedness, with the words above bit 63 of
// one declared wider than 64 bits. Empty when the registered module declares
// no such parameter where the expression stands, when it is a type, real or
// string parameter, or when `value` is not the value it resolved to. Defined
// in const_eval_bits.cpp.
std::optional<ConstVal> RegisteredParamValue(std::string_view name,
                                             int64_t value);

// §6.20.2 with §23.10.1 and §23.10.2: the words above bit 63 of the value
// `expr` folds to against `scope`, recorded on `pd` as
// RtlirParamDecl::resolved_high_words for RegisteredParamValue to read where
// the parameter is declared wider than 64 bits -- read at the declared width
// and signedness, as an override value is converted to the parameter's range
// -- and, for a parameter declared with neither type nor range, the value's
// own self-determined width and signedness as RtlirParamDecl::value_width
// and value_is_signed, §6.20.2's implied range; all cleared where the fold
// carries none or does not agree with pd.resolved_value on the low word. The
// elaborator calls this wherever it records a resolved value the fold of an
// expression gave: an instance override's, folded in the instantiating
// module, and a defparam's and the parameters it makes over, whose own
// expressions RegisteredParamValue could not refold there. Defined in
// const_eval_bits.cpp.
void RecordResolvedHighWords(RtlirParamDecl& pd, const Expr* expr,
                             const ScopeMap& scope);

// §11.5.1: the packed range the parameter `name` was declared with, taken from
// the module a live ParamRangeRegistryGuard installed. Empty when no guard is
// live, when the module declares no such parameter, or when that parameter's
// declaration carries no packed range -- in each of those cases the value is
// addressed as [width-1:0], where an index and a bit offset are the same
// number.
std::optional<PackedRange> RegisteredParamRange(std::string_view name);

// §23.9: the generate block prefixes in force where the expression being folded
// stands, outermost first, as a live RegisteredGenScopeGuard installed them.
// Empty for an expression among a module's own items, which is what a
// ParamRangeRegistryGuard leaves behind when it installs a module. A reader
// matching a parameter by name hands this to ParamVisibleFromScopes to find out
// whether the declaration it matched is one this expression may name.
const std::vector<std::string_view>& RegisteredGenPrefixes();

// The module a live ParamRangeRegistryGuard installed, or null when none is
// live. A ScopeMap gives a name a value and says nothing about how it was
// declared, so this is what a fold consults when the declaration is what
// decides the answer.
const RtlirModule* RegisteredModule();

// Whether every element of `elems` is a constant expression. Vacuously true for
// an empty list, which is what an argument-list test alone answers for a call
// that takes no arguments.
bool AllElementsConstant(const std::vector<Expr*>& elems,
                         const ScopeMap& scope);

// §11.2.1: the value of a constant built-in method call (§5.13), evaluated at
// elaboration time from the declaration behind the operand. Empty when `expr`
// is not a built-in method call and when it is one this implementation cannot
// evaluate; the two are not distinguished, because a call that does not
// evaluate is not one a constant expression may hold.
std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr);

// Whether `expr` is a constant built-in method call, or empty when it is not a
// built-in method call at all. The empty answer is what lets a member access
// spelling one of the method names fall through to the ordinary compound
// parameter lookup, since a class may declare a parameter called `size`.
std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope);

}  // namespace delta
