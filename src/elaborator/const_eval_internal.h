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

std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                            const ScopeMap& scope);
std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope);
std::optional<ConstVal> ConstEvalLiteral(const Expr* expr);
std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr);
std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                           const ScopeMap& scope);
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

// §11.4.10 with §11.4.8, §11.4.3, §11.4.4, §11.4.5 and §11.4.7: a shift, a
// bitwise operator, an arithmetic operator, a relational, an equality or a
// logical operator applied across every word of `lhs` and `rhs`, at width
// `width`, for an operand that carries bits past 63; a comparison and a
// logical operator answer one bit. Empty for any other operator -- the case
// equality and wildcard operators -- which the 64-bit fold answers on the
// low word, and for a quotient or a remainder by zero and a power §11.4.3
// makes x. Defined in const_eval_wide.cpp.
std::optional<ConstVal> EvalWideBinary(TokenKind op, const ConstVal& lhs,
                                       const ConstVal& rhs, uint32_t width);

// §11.4.3 (printed pages 275-276) with §11.4.3.1: the product, the quotient,
// the remainder or the power of `lhs` and `rhs` at width `width`, worked
// across every word of them -- the quotient truncated toward zero, the
// remainder with the sign of the first operand, the power by Table 11-4 --
// and cut to the width as §11.6.1 cuts an arithmetic result. Empty for a
// divisor of zero and for a base of zero under a negative exponent, which
// the clause makes x, as the 64-bit fold answers them. `op` is one of the
// four; 994404a79 folded each on the low word. Defined in
// const_eval_wide_arith.cpp.
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
