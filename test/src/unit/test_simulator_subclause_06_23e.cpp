#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <string>
#include <string_view>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §6.23 (printed page 138): a type reference to an expression stands for the
// expression's self-determined type, the expression left unevaluated, and two
// type references compared with ==, !=, === or !== give whether the two types
// match (§6.22.1). Each comparison below holds against the type its operand
// has by §11.6.1's widths, §11.8.1's signing, §11.3.1's real operands and
// §11.3.4's 2- and 4-state operands, or fails against the type nearest it.
struct Comparison {
  const char* text;
  bool holds;
};

// The subroutines declared outside the module that the calls compared read:
// a package's function and DPI import, and the compilation unit's; and a
// package's class.
constexpr const char* kOutsideTheModule =
    "package pk;\n"
    "  function automatic shortint pf(); return 0; endfunction\n"
    "  import \"DPI-C\" function longint pd();\n"
    "  class KC;\n"
    "    shortint kv;\n"
    "    static function longint ksf(); return 0; endfunction\n"
    "  endclass\n"
    "  class KD extends KC;\n"
    "  endclass\n"
    "endpackage\n"
    "function automatic byte uf(); return 0; endfunction\n"
    "import \"DPI-C\" function real ud();\n";

// The operands every comparison reads.
constexpr const char* kOperands =
    "  import pk::pf;\n"
    "  import \"DPI-C\" function shortreal md(input int n);\n"
    "  byte a;\n"
    "  bit [7:0] b;\n"
    "  logic [3:0] c;\n"
    "  shortint s;\n"
    "  logic [7:0] v;\n"
    "  logic signed [7:0] sv;\n"
    "  logic [3:0][7:0] pk;\n"
    "  int i;\n"
    "  logic [5:0] x;\n"
    "  real rl;\n"
    "  shortreal srl;\n"
    "  bit flag;\n"
    "  typedef struct packed { byte f; logic [2:0] g; } ps_t;\n"
    "  ps_t p;\n"
    "  bit [5:0] arr [4];\n"
    "  typedef enum {E0, E1} e_t;\n"
    "  localparam byte P = 3;\n"
    "  e_t en;\n"
    "  string str;\n"
    "  int dyn [];\n"
    "  int que [$];\n"
    "  byte bq [$];\n"
    "  int aa [string];\n"
    "  shortint ia [4];\n"
    "  int ai [byte];\n"
    "  int ab [bit [3:0]];\n"
    "  logic [3:0] u [2];\n"
    "  wire [3:0] un [2];\n"
    "  int m [2][3];\n"
    "  typedef logic [3:0] u_t [2];\n"
    "  typedef logic [3:0] ur_t [0:1];\n"
    "  typedef logic [3:0] ud_t [1:0];\n"
    "  typedef bit [3:0] ub_t [2];\n"
    "  typedef u_t ua_t;\n"
    "  typedef int i3_t [3];\n"
    "  typedef int i3r_t [1:3];\n"
    "  typedef i3_t i23_t [2];\n"
    "  typedef int dyn_t [];\n"
    "  typedef int iq_t [$];\n"
    "  typedef int aas_t [string];\n"
    "  typedef int aai_t [int];\n"
    "  typedef byte bq_t [$];\n"
    "  typedef bit [5:0] b6q_t [$];\n"
    "  typedef int i3q_t [$][3];\n"
    "  class C;\n"
    "    byte x;\n"
    "    logic [3:0] y [2];\n"
    "    function shortint f(); return 0; endfunction\n"
    "    static function bit [2:0] sf(); return 0; endfunction\n"
    "    virtual function real vf(); return 0; endfunction\n"
    "  endclass\n"
    "  class D extends C;\n"
    "    int z;\n"
    "  endclass\n"
    "  class PC #(int W = 4, type T = byte);\n"
    "    logic [W-1:0] w;\n"
    "    T t;\n"
    "  endclass\n"
    "  typedef C c_t;\n"
    "  typedef PC #(8) pc8_t;\n"
    "  C h;\n"
    "  D dh;\n"
    "  pk::KC kh;\n"
    "  PC #(8) p8;\n"
    "  PC #(8, int) p8i;\n"
    "  PC pd;\n";

// §11.6.1 with §11.8.1: an arithmetic operator is as wide as its wider
// operand, signed where both are and 4-state where either is; a unary minus
// is its operand's type.
constexpr std::array kArithmetic = {
    Comparison{"type(a + b) == type(bit [7:0])", true},
    Comparison{"type(a + b) == type(byte)", false},
    Comparison{"type(a + s) == type(shortint)", true},
    Comparison{"type(a + s) == type(bit [15:0])", false},
    Comparison{"type(a + c) == type(logic [7:0])", true},
    Comparison{"type(a + c) == type(bit [7:0])", false},
    Comparison{"type(-a) == type(byte)", true},
    Comparison{"type(-a) == type(bit [7:0])", false},
    Comparison{"type(a + b) == type(b + a)", true},
    Comparison{"type(a + b) != type(a + c)", true},
};

// §11.6.1: a bitwise operator sizes as an arithmetic one does, and a shift is
// its left operand's type, 4-state where either operand is.
constexpr std::array kBitwiseAndShift = {
    Comparison{"type(a & b) == type(bit [7:0])", true},
    Comparison{"type(a & c) == type(bit [7:0])", false},
    Comparison{"type(a << b) == type(byte)", true},
    Comparison{"type(a << b) == type(bit [7:0])", false},
    Comparison{"type(a >>> c) == type(logic signed [7:0])", true},
    Comparison{"type(a >>> c) == type(byte)", false},
};

// §11.6.1 with §11.8.1: a relational, equality, logical, reduction or
// set membership operator is one unsigned bit.
constexpr std::array kOneBitResults = {
    Comparison{"type(a < b) == type(bit)", true},
    Comparison{"type(a < b) == type(logic)", false},
    Comparison{"type(a == c) == type(logic)", true},
    Comparison{"type(a == c) == type(bit)", false},
    Comparison{"type(a && b) == type(bit)", true},
    Comparison{"type(a && b) == type(bit [7:0])", false},
    Comparison{"type(&b) == type(bit)", true},
    Comparison{"type(!c) == type(logic)", true},
    Comparison{"type(b inside {a, b}) == type(bit)", true},
    Comparison{"type(c inside {a}) == type(bit)", false},
};

// §11.5.1 with §11.8.1 and §7.4.1: a bit-select is one bit and a part-select
// as many bits as it names, unsigned and of the vector's state; an element of
// a packed array is the array's element type.
constexpr std::array kSelects = {
    Comparison{"type(v[3]) == type(logic)", true},
    Comparison{"type(v[3]) == type(bit)", false},
    Comparison{"type(v[7:4]) == type(logic [3:0])", true},
    Comparison{"type(v[7:4]) == type(logic [4:0])", false},
    Comparison{"type(sv[i +: 4]) == type(logic [3:0])", true},
    Comparison{"type(sv[i +: 4]) == type(logic signed [3:0])", false},
    Comparison{"type(sv[7 -: 3]) == type(logic [2:0])", true},
    Comparison{"type(pk[1]) == type(logic [7:0])", true},
    Comparison{"type(pk[1]) == type(logic [31:0])", false},
    Comparison{"type(pk[2:1]) == type(logic [15:0])", true},
};

// §7.2 and §7.4.2: a member of a structure is the type it was declared with,
// and an element of an unpacked array the array's element type.
constexpr std::array kMembersAndElements = {
    Comparison{"type(p.g) == type(logic [2:0])", true},
    Comparison{"type(p.g) == type(bit [2:0])", false},
    Comparison{"type(p.f) == type(byte)", true},
    Comparison{"type(p.f) == type(bit [7:0])", false},
    Comparison{"type(p.f[0]) == type(bit)", true},
    Comparison{"type(arr[1]) == type(bit [5:0])", true},
    Comparison{"type(arr[1]) == type(bit [4:0])", false},
    Comparison{"type(arr[1][2]) == type(bit)", true},
};

// §11.4.12 and §11.4.12.1: a concatenation is unsigned and as wide as its
// operands together, a replication its count of copies of them; §11.4.11: a
// conditional is as wide as its wider result, signed where both are and
// 4-state where its condition or a result is.
constexpr std::array kConcatenationsAndConditionals = {
    Comparison{"type({a, b}) == type(bit [15:0])", true},
    Comparison{"type({a, b}) == type(shortint)", false},
    Comparison{"type({2{c}}) == type(logic [7:0])", true},
    Comparison{"type({2{c}}) == type(logic [3:0])", false},
    Comparison{"type({a, c}) == type(logic [11:0])", true},
    Comparison{"type(flag ? a : b) == type(bit [7:0])", true},
    Comparison{"type(flag ? a : b) == type(byte)", false},
    Comparison{"type(flag ? a : s) == type(shortint)", true},
    Comparison{"type(c[0] ? a : b) == type(logic [7:0])", true},
};

// §6.24.1: a cast is the type it names, a signing cast its operand with the
// signing it names, and a size cast its operand's signing and state at the
// size it names.
constexpr std::array kCasts = {
    Comparison{"type(byte'(b)) == type(byte)", true},
    Comparison{"type(byte'(b)) == type(bit [7:0])", false},
    Comparison{"type(signed'(v)) == type(logic signed [7:0])", true},
    Comparison{"type(signed'(v)) == type(logic [7:0])", false},
    Comparison{"type(unsigned'(a)) == type(bit [7:0])", true},
    Comparison{"type(4'(b)) == type(bit [3:0])", true},
    Comparison{"type(4'(a)) == type(bit signed [3:0])", true},
    Comparison{"type(e_t'(i)) == type(e_t)", true},
    Comparison{"type(e_t'(i)) == type(int)", false},
    Comparison{"type(type(c)'(b)) == type(logic [3:0])", true},
};

// §11.4.2 and §11.3.6: an increment, a decrement and an assignment are the
// type of the variable they would change, with none of them carried out.
constexpr std::array kIncrementsAndAssignments = {
    Comparison{"type(i++) == type(int)", true},
    Comparison{"type(i++) == type(integer)", false},
    Comparison{"type(--i) == type(int)", true},
    Comparison{"type((x += 3)) == type(logic [5:0])", true},
    Comparison{"type((x += 3)) == type(logic [6:0])", false},
    Comparison{"type((x = b)) == type(logic [5:0])", true},
};

// A system function is the type its clause gives its result: an integer for
// $bits (§20.6.2) and $clog2 (§20.8.1), an int for $countones (§20.9), a bit
// for $isunknown (§20.9) and a real for $itor (§20.5); $signed and $unsigned
// (§11.7) are their argument with the signing each names.
constexpr std::array kSystemFunctions = {
    Comparison{"type($bits(x)) == type(integer)", true},
    Comparison{"type($bits(x)) == type(int)", false},
    Comparison{"type($clog2(8)) == type(integer)", true},
    Comparison{"type($signed(v)) == type(logic signed [7:0])", true},
    Comparison{"type($signed(v)) == type(logic [7:0])", false},
    Comparison{"type($unsigned(a)) == type(bit [7:0])", true},
    Comparison{"type($countones(v)) == type(int)", true},
    Comparison{"type($isunknown(v)) == type(bit)", true},
    Comparison{"type($itor(i)) == type(real)", true},
};

// §5.7.1: an integer literal is as wide as its size, or 32 bits unsized,
// signed where it is decimal or carries the s designator, and 4-state; an
// unbased unsized literal is one bit where it is self-determined. §5.7.2 and
// §5.8: a real or time literal is real. §5.9: a string literal is an unsigned
// integral value of eight bits a character.
constexpr std::array kLiterals = {
    Comparison{"type(4'b1010) == type(logic [3:0])", true},
    Comparison{"type(4'b1010) == type(bit [3:0])", false},
    Comparison{"type(-4'sd3) == type(logic signed [3:0])", true},
    Comparison{"type(-4'sd3) == type(logic [3:0])", false},
    Comparison{"type(5) == type(integer)", true},
    Comparison{"type(5) == type(int)", false},
    Comparison{"type('1) == type(logic)", true},
    Comparison{"type(1.5) == type(real)", true},
    Comparison{"type(1.5) == type(shortreal)", false},
    Comparison{"type(1ns) == type(real)", true},
    Comparison{"type(\"ab\") == type(logic [15:0])", true},
    Comparison{"type(\"ab\") == type(logic [7:0])", false},
};

// §11.3.1: an operator with a real operand is real, and one with a shortreal
// operand and no real one is shortreal.
constexpr std::array kRealOperands = {
    Comparison{"type(rl * 2) == type(real)", true},
    Comparison{"type(srl + b) == type(shortreal)", true},
    Comparison{"type(srl + b) == type(real)", false},
    Comparison{"type(srl + rl) == type(real)", true},
    Comparison{"type(rl ** 2) == type(real)", true},
    Comparison{"type(flag ? rl : a) == type(real)", true},
};

// §6.20.2 and §6.19.3: a parameter is the type it was declared with, and an
// enumeration's named constant is of the enumeration's type.
constexpr std::array kParametersAndConstants = {
    Comparison{"type(P) == type(byte)", true},
    Comparison{"type(P) == type(bit [7:0])", false},
    Comparison{"type(P + b) == type(bit [7:0])", true},
    Comparison{"type(E1) == type(e_t)", true},
    Comparison{"type(E1) == type(int)", false},
};

// §6.19.5: first, last, next and prev give the enumeration's type, num an int
// and name a string, called on a variable or a named constant, and with or
// without the parentheses §5.13 lets a call with no arguments leave out.
constexpr std::array kEnumerationMethods = {
    Comparison{"type(en.first()) == type(e_t)", true},
    Comparison{"type(en.first()) == type(int)", false},
    Comparison{"type(en.last) == type(e_t)", true},
    Comparison{"type(en.next(2)) == type(e_t)", true},
    Comparison{"type(E1.prev()) == type(e_t)", true},
    Comparison{"type(en.num()) == type(int)", true},
    Comparison{"type(en.num) == type(e_t)", false},
    Comparison{"type(en.name()) == type(string)", true},
    Comparison{"type(en.name()) == type(int)", false},
};

// §6.16.1 to §6.16.10: len, compare and icompare give an int, getc a byte,
// toupper, tolower and substr a string, atoi, atohex, atooct and atobin an
// integer, and atoreal a real, a method of a method's result included.
constexpr std::array kStringMethods = {
    Comparison{"type(str.len()) == type(int)", true},
    Comparison{"type(str.len) == type(integer)", false},
    Comparison{"type(str.compare(\"a\")) == type(int)", true},
    Comparison{"type(str.icompare(str)) == type(int)", true},
    Comparison{"type(str.getc(0)) == type(byte)", true},
    Comparison{"type(str.getc(0)) == type(bit [7:0])", false},
    Comparison{"type(str.toupper()) == type(string)", true},
    Comparison{"type(str.tolower) == type(string)", true},
    Comparison{"type(str.substr(0, 1)) == type(string)", true},
    Comparison{"type(str.atoi()) == type(integer)", true},
    Comparison{"type(str.atohex()) == type(int)", false},
    Comparison{"type(str.atooct()) == type(integer)", true},
    Comparison{"type(str.atobin()) == type(integer)", true},
    Comparison{"type(str.atoreal()) == type(real)", true},
    Comparison{"type(str.tolower().len()) == type(int)", true},
};

// §7.5.2, §7.10.2.1 and §7.9.1 to §7.9.7: size gives an int, as do an
// associative array's num, exists, first, last, next and prev; §7.10.2.4 and
// §7.10.2.5: pop_front and pop_back give the queue's element type.
constexpr std::array kArrayMethods = {
    Comparison{"type(dyn.size()) == type(int)", true},
    Comparison{"type(dyn.size) == type(integer)", false},
    Comparison{"type(que.size()) == type(int)", true},
    Comparison{"type(aa.size()) == type(int)", true},
    Comparison{"type(aa.num()) == type(int)", true},
    Comparison{"type(aa.exists(\"k\")) == type(int)", true},
    Comparison{"type(aa.exists(\"k\")) == type(bit)", false},
    Comparison{"type(aa.first(str)) == type(int)", true},
    Comparison{"type(aa.last(str)) == type(int)", true},
    Comparison{"type(aa.next(str)) == type(int)", true},
    Comparison{"type(aa.prev(str)) == type(int)", true},
    Comparison{"type(que.pop_front()) == type(int)", true},
    Comparison{"type(bq.pop_back()) == type(byte)", true},
    Comparison{"type(bq.pop_back()) == type(int)", false},
};

// §7.12.3: a reduction method gives the array's element type, or, with a with
// clause, the type of its expression, the iterator named item or named by the
// method's argument; §7.12.4: the iterator's index method gives an int, or an
// associative array's index type.
constexpr std::array kReductionMethods = {
    Comparison{"type(ia.sum()) == type(shortint)", true},
    Comparison{"type(ia.sum()) == type(int)", false},
    Comparison{"type(ia.product) == type(shortint)", true},
    Comparison{"type(arr.and()) == type(bit [5:0])", true},
    Comparison{"type(arr.or()) == type(logic [5:0])", false},
    Comparison{"type(dyn.xor()) == type(int)", true},
    Comparison{"type(que.sum with (item[0])) == type(bit)", true},
    Comparison{"type(arr.sum with (int'(item))) == type(int)", true},
    Comparison{"type(arr.sum with (int'(item))) == type(bit [5:0])", false},
    Comparison{"type(arr.product(x) with (x[1:0])) == type(bit [1:0])", true},
    Comparison{"type(ia.sum with (item.index)) == type(int)", true},
    Comparison{"type(ia.sum with (item.index)) == type(shortint)", false},
    Comparison{"type(ai.sum with (item.index)) == type(byte)", true},
    Comparison{"type(ai.sum with (item.index)) == type(int)", false},
    Comparison{"type(ab.sum with (item.index)) == type(bit [3:0])", true},
    Comparison{"type(ab.sum with (item.index)) == type(logic [3:0])", false},
};

// §26.3: a package's function gives its return type, called through the
// package or imported, as do a function the compilation unit declares
// (§3.12.1) and an imported DPI function (§35.5.4), whether the module, a
// package or the compilation unit imports it.
constexpr std::array kSubroutineCalls = {
    Comparison{"type(pk::pf()) == type(shortint)", true},
    Comparison{"type(pk::pf()) == type(int)", false},
    Comparison{"type(pf()) == type(shortint)", true},
    Comparison{"type(uf()) == type(byte)", true},
    Comparison{"type(uf()) == type(bit [7:0])", false},
    Comparison{"type(md(1)) == type(shortreal)", true},
    Comparison{"type(md(1)) == type(real)", false},
    Comparison{"type(pk::pd()) == type(longint)", true},
    Comparison{"type(ud()) == type(real)", true},
};

// §6.22.1(f) with §7.4.2: two unpacked array types match where they are the
// same kind of array with matching element types, matching index types where
// associative, and the same bounds where fixed in size, `[2]` being `[0:1]`.
// An element of a multidimensional array is an array of the dimensions left,
// and a typedef renaming an array typedef, or writing dimensions on one, adds
// none of its own to those it names, or puts its own outside them (§7.4.4).
constexpr std::array kUnpackedArrays = {
    Comparison{"type(u) == type(u)", true},
    Comparison{"type(u) == type(un)", true},
    Comparison{"type(u) == type(u_t)", true},
    Comparison{"type(u) == type(ur_t)", true},
    Comparison{"type(u) == type(ua_t)", true},
    Comparison{"type(u) == type(ud_t)", false},
    Comparison{"type(u) == type(ub_t)", false},
    Comparison{"type(u) == type(logic [3:0])", false},
    Comparison{"type(m[0]) == type(i3_t)", true},
    Comparison{"type(m[1]) == type(m[0])", true},
    Comparison{"type(m[0]) == type(i3r_t)", false},
    Comparison{"type(m) == type(i23_t)", true},
    Comparison{"type(m) == type(i3_t)", false},
    Comparison{"type(dyn) == type(dyn_t)", true},
    Comparison{"type(dyn) == type(iq_t)", false},
    Comparison{"type(dyn) == type(int)", false},
    Comparison{"type(que) == type(iq_t)", true},
    Comparison{"type(que) == type(dyn_t)", false},
    Comparison{"type(aa) == type(aas_t)", true},
    Comparison{"type(aa) == type(aai_t)", false},
    Comparison{"type(ai) == type(aas_t)", false},
};

// §7.12.1: an array locator method gives a queue: of the array's element type
// for find, find_first, find_last, min, max and unique, and of int for
// find_index, find_first_index, find_last_index and unique_index, or of the
// index type where the array is associative.
constexpr std::array kArrayLocators = {
    Comparison{"type(arr.find with (item > 1)) == type(b6q_t)", true},
    Comparison{"type(arr.find with (item > 1)) == type(bit [5:0])", false},
    Comparison{"type(arr.find_first with (item > 1)) == type(b6q_t)", true},
    Comparison{"type(arr.find_last(x) with (x > 1)) == type(b6q_t)", true},
    Comparison{"type(arr.min()) == type(b6q_t)", true},
    Comparison{"type(arr.max) == type(b6q_t)", true},
    Comparison{"type(arr.unique()) == type(b6q_t)", true},
    Comparison{"type(arr.unique()) == type(iq_t)", false},
    Comparison{"type(bq.find with (item > 1)) == type(bq_t)", true},
    Comparison{"type(m.unique()) == type(i3q_t)", true},
    Comparison{"type(arr.find_index with (item > 1)) == type(iq_t)", true},
    Comparison{"type(arr.find_index with (item > 1)) == type(b6q_t)", false},
    Comparison{"type(arr.find_first_index with (item > 1)) == type(iq_t)",
               true},
    Comparison{"type(arr.find_last_index with (item > 1)) == type(iq_t)", true},
    Comparison{"type(arr.unique_index()) == type(iq_t)", true},
    Comparison{"type(ai.find_index with (item > 1)) == type(bq_t)", true},
    Comparison{"type(ai.find_index with (item > 1)) == type(iq_t)", false},
};

// §6.22.1 with §8.4 and §8.25: a class handle is of its class, which matches
// itself, a typedef of it and no other class, a class it extends included;
// a specialization of a parameterized class matches another only where each
// parameter takes the same value or type, a default given or left out alike,
// and the unadorned name is the default specialization.
constexpr std::array kClassHandles = {
    Comparison{"type(h) == type(C)", true},
    Comparison{"type(h) == type(D)", false},
    Comparison{"type(dh) == type(D)", true},
    Comparison{"type(dh) == type(C)", false},
    Comparison{"type(h) == type(c_t)", true},
    Comparison{"type(kh) == type(pk::KC)", true},
    Comparison{"type(kh) == type(C)", false},
    Comparison{"type(p8) == type(PC #(8))", true},
    Comparison{"type(p8) == type(PC #(16))", false},
    Comparison{"type(p8) == type(PC #(8, byte))", true},
    Comparison{"type(p8) == type(pc8_t)", true},
    Comparison{"type(p8) == type(p8i)", false},
    Comparison{"type(p8i) == type(PC #(8, int))", true},
    Comparison{"type(pd) == type(PC #())", true},
    Comparison{"type(pd) == type(PC #(4))", true},
    Comparison{"type(pd) == type(p8)", false},
};

// §8.5, §8.6, §8.10 and §8.13: a property read through a handle is of the
// type it is declared with, under the handle's specialization, and a method
// called through a handle or a class scope gives its return type, a member
// the class inherits included.
constexpr std::array kClassMembers = {
    Comparison{"type(h.x) == type(byte)", true},
    Comparison{"type(h.x) == type(bit [7:0])", false},
    Comparison{"type(dh.x) == type(byte)", true},
    Comparison{"type(dh.z) == type(int)", true},
    Comparison{"type(h.y) == type(u_t)", true},
    Comparison{"type(h.y) == type(logic [3:0])", false},
    Comparison{"type(kh.kv) == type(shortint)", true},
    Comparison{"type(p8.w) == type(logic [7:0])", true},
    Comparison{"type(p8.w) == type(logic [3:0])", false},
    Comparison{"type(pd.w) == type(logic [3:0])", true},
    Comparison{"type(p8i.t) == type(int)", true},
    Comparison{"type(pd.t) == type(byte)", true},
    Comparison{"type(h.f()) == type(shortint)", true},
    Comparison{"type(h.f()) == type(int)", false},
    Comparison{"type(dh.f()) == type(shortint)", true},
    Comparison{"type(dh.vf()) == type(real)", true},
    Comparison{"type(h.sf()) == type(bit [2:0])", true},
    Comparison{"type(C::sf()) == type(bit [2:0])", true},
    Comparison{"type(C::sf()) == type(logic [2:0])", false},
    Comparison{"type(D::sf()) == type(bit [2:0])", true},
    Comparison{"type(dh.sf()) == type(logic [2:0])", false},
    Comparison{"type(pk::KC::ksf()) == type(longint)", true},
    Comparison{"type(pk::KC::ksf()) == type(int)", false},
    Comparison{"type(pk::KD::ksf()) == type(longint)", true},
};

struct ComparisonGroup {
  const char* name;
  std::span<const Comparison> comparisons;
  // §11.3.6 (printed page 275): an assignment operator stands only in an
  // expression within a procedural statement, a type reference's included.
  bool procedural_only = false;
};

constexpr std::array kGroups = {
    ComparisonGroup{"arithmetic", kArithmetic},
    ComparisonGroup{"bitwise and shift", kBitwiseAndShift},
    ComparisonGroup{"one-bit results", kOneBitResults},
    ComparisonGroup{"selects", kSelects},
    ComparisonGroup{"members and elements", kMembersAndElements},
    ComparisonGroup{"concatenations and conditionals",
                    kConcatenationsAndConditionals},
    ComparisonGroup{"casts", kCasts},
    ComparisonGroup{"increments and assignments", kIncrementsAndAssignments,
                    true},
    ComparisonGroup{"system functions", kSystemFunctions},
    ComparisonGroup{"literals", kLiterals},
    ComparisonGroup{"real operands", kRealOperands},
    ComparisonGroup{"parameters and constants", kParametersAndConstants},
    ComparisonGroup{"enumeration methods", kEnumerationMethods},
    ComparisonGroup{"string methods", kStringMethods},
    ComparisonGroup{"array methods", kArrayMethods},
    ComparisonGroup{"reduction methods", kReductionMethods},
    ComparisonGroup{"subroutine calls", kSubroutineCalls},
    ComparisonGroup{"unpacked arrays", kUnpackedArrays},
    ComparisonGroup{"array locators", kArrayLocators},
    ComparisonGroup{"class handles", kClassHandles},
    ComparisonGroup{"class members", kClassMembers},
};

// Where §6.23 lets a comparison of type references stand: a procedural if's
// condition, a continuous assignment's right-hand side, a generate if's
// condition (§27.5) and a localparam's value (§6.20.4).
enum class Place : std::uint8_t {
  kProceduralIf,
  kContinuousAssignment,
  kGenerateIf,
  kParam
};

// A module declaring the operands and writing each comparison of `group` at
// `place`, the k-th setting the bit of r k places below its most significant.
std::string ModuleComparing(std::span<const Comparison> group, Place place) {
  const size_t kCount = group.size();
  std::string src = std::format("{}module t;\n{}  bit [{}:0] r;\n",
                                kOutsideTheModule, kOperands, kCount - 1);
  std::string listed;
  std::string body;
  for (size_t k = 0; k < kCount; ++k) {
    const std::string_view kText = group[k].text;
    const std::string kBit = std::format("r[{}]", kCount - 1 - k);
    const std::string_view kSeparator = k == 0 ? "" : ", ";
    switch (place) {
      case Place::kProceduralIf:
        body += std::format("    if ({}) {} = 1'b1;\n", kText, kBit);
        break;
      case Place::kContinuousAssignment:
        listed += std::format("{}{}", kSeparator, kText);
        break;
      case Place::kGenerateIf:
        src += std::format(
            "  if ({0}) begin : g{1} initial {2} = 1'b1; end\n"
            "  else begin : h{1} initial {2} = 1'b0; end\n",
            kText, k, kBit);
        break;
      default:
        src += std::format("  localparam bit L{} = {};\n", k, kText);
        listed += std::format("{}L{}", kSeparator, k);
        break;
    }
  }
  if (place == Place::kProceduralIf)
    src += std::format("  initial begin\n{}  end\n", body);
  if (place == Place::kContinuousAssignment)
    src += std::format("  assign r = {{{}}};\n", listed);
  if (place == Place::kParam)
    src += std::format("  initial r = {{{}}};\n", listed);
  return src + "endmodule\n";
}

// The value r takes where each comparison of `group` gives what the standard
// says it gives.
uint64_t ExpectedBits(std::span<const Comparison> group) {
  uint64_t bits = 0;
  for (const Comparison& comparison : group) {
    bits = (bits << 1) | (comparison.holds ? 1u : 0u);
  }
  return bits;
}

void ExpectEveryGroupAt(Place place) {
  for (const ComparisonGroup& group : kGroups) {
    if (group.procedural_only && place != Place::kProceduralIf) continue;
    SCOPED_TRACE(group.name);
    EXPECT_EQ(RunAndGet(ModuleComparing(group.comparisons, place), "r"),
              ExpectedBits(group.comparisons));
  }
}

TEST(TypeOfExpressionCompareSim, ComparisonInAProceduralIf) {
  ExpectEveryGroupAt(Place::kProceduralIf);
}

TEST(TypeOfExpressionCompareSim, ComparisonInAContinuousAssignment) {
  ExpectEveryGroupAt(Place::kContinuousAssignment);
}

TEST(TypeOfExpressionCompareSim, ComparisonSelectsAGenerateBranch) {
  ExpectEveryGroupAt(Place::kGenerateIf);
}

TEST(TypeOfExpressionCompareSim, ComparisonSetsAParameter) {
  ExpectEveryGroupAt(Place::kParam);
}

// §6.23: the expression a type reference names is not evaluated, so neither
// the increment nor the operator assignment a comparison names changes the
// variable it would write.
TEST(TypeOfExpressionCompareSim, ComparedExpressionIsNotEvaluated) {
  const std::string kSrc =
      "module t;\n"
      "  int i = 5;\n"
      "  logic [5:0] x = 1;\n"
      "  bit [1:0] r;\n"
      "  initial r = {type(i++) == type(int), type((x += 3)) == type(int)};\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b10u);
  EXPECT_EQ(RunAndGet(kSrc, "i"), 5u);
  EXPECT_EQ(RunAndGet(kSrc, "x"), 1u);
}

// §6.23 with §7.10.2.4: nor is a method call, so the queue a comparison would
// pop from keeps both its elements.
TEST(TypeOfExpressionCompareSim, ComparedMethodCallIsNotEvaluated) {
  const std::string kSrc =
      "module t;\n"
      "  int que [$] = {1, 2};\n"
      "  bit r;\n"
      "  int n;\n"
      "  initial begin\n"
      "    r = type(que.pop_front()) == type(int);\n"
      "    n = que.size();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 1u);
  EXPECT_EQ(RunAndGet(kSrc, "n"), 2u);
}

// §6.23 with §27.5: a name in the expression is the value the generate block
// the comparison stands in declares, where the module declares another of the
// name.
TEST(TypeOfExpressionCompareSim, OperandOfAGenerateBlockIsTypedInTheBlock) {
  const std::string kSrc =
      "module t;\n"
      "  wire [7:0] n;\n"
      "  bit [2:0] r;\n"
      "  if (1) begin : g\n"
      "    wire [0:3] n;\n"
      "    initial r = {type(n[0:1]) == type(logic [1:0]),\n"
      "                 type(n + n) == type(logic [3:0]),\n"
      "                 type(n + n) == type(logic [7:0])};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b110u);
}

// §6.23: a declaration whose type is a type reference to an expression takes
// the expression's self-determined type: 2-state where every operand is, so x
// assigned to it reads as 0, signed where every operand is, as wide as §11.6.1
// makes it, and real where an operand is.
TEST(TypeOfExpressionDeclarationSim, DeclarationTakesTheSelfDeterminedType) {
  const std::string kSrc =
      "module t;\n"
      "  byte a;\n"
      "  bit [7:0] b;\n"
      "  logic [3:0] c;\n"
      "  shortint s;\n"
      "  real rl;\n"
      "  var type(a + b) d;\n"
      "  var type(a + s) e;\n"
      "  var type(a + c) f;\n"
      "  var type({a, b}) h;\n"
      "  var type(rl * 2) g;\n"
      "  bit [18:0] r;\n"
      "  initial begin\n"
      "    d = 'x;\n"
      "    e = -1;\n"
      "    f = 'x;\n"
      "    h = 'x;\n"
      "    g = 1.25;\n"
      "    r = {$isunknown(d), e < 0, $isunknown(f), $isunknown(h),\n"
      "         5'($bits(d)), 5'($bits(e)), 5'($bits(h))};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b0110'01000'10000'10000u);
  EXPECT_EQ(RunAndGetReal(kSrc, "g"), 1.25);
}

// §6.23: a declaration written with a type reference to a call takes the type
// the call gives: a string's len an int, 2-state and 32 bits wide (§6.16.1); a
// queue's pop_front its signed byte element (§7.10.2.4); an enumeration's next
// the enumeration, 3 bits wide (§6.19.5.3); a package's function its shortint
// (§26.3); and an imported DPI function its real (§35.5.4).
TEST(TypeOfExpressionDeclarationSim, DeclarationTakesACallsType) {
  const std::string kSrc =
      "package pk;\n"
      "  function automatic shortint pf(); return 0; endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import \"DPI-C\" function real md();\n"
      "  string str;\n"
      "  byte bq [$];\n"
      "  typedef enum logic [2:0] {A, B} e_t;\n"
      "  e_t en;\n"
      "  var type(str.len()) d;\n"
      "  var type(bq.pop_front()) e;\n"
      "  var type(en.next()) f;\n"
      "  var type(pk::pf()) g;\n"
      "  var type(md()) h;\n"
      "  bit [24:0] r;\n"
      "  initial begin\n"
      "    d = 'x;\n"
      "    e = -1;\n"
      "    h = 1.25;\n"
      "    r = {$isunknown(d), 6'($bits(d)), e < 0, 6'($bits(e)),\n"
      "         6'($bits(f)), 5'($bits(g))};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b0'100000'1'001000'000011'10000u);
  EXPECT_EQ(RunAndGetReal(kSrc, "h"), 1.25);
}

// §6.23 with §7.4.4: a declaration written with a type reference to an
// unpacked array is an array of the same kind, element and bounds, and the
// dimensions the declaration writes after its name stand outside those. Each
// operand below is declared with, and its probe run, in a module, a
// procedural block, a function and a generate block; written with `[3]`
// after the name, the declaration is three of the operand's array, the first
// of which is as large as an array of the operand's type starts, empty where
// that is variable in size.
struct DeclaredArray {
  const char* operand;
  const char* probe;
  uint64_t expected;
  uint64_t initial_size;
};

constexpr std::array kDeclaredArrays = {
    DeclaredArray{"u", "n = $size(d) * 10 + $bits(d[0]);", 24, 2},
    DeclaredArray{"m[0]", "n = $size(d) * 100 + $bits(d[0]);", 332, 3},
    DeclaredArray{"m", "n = $size(d) * 10 + $size(d[0]);", 23, 2},
    DeclaredArray{"dyn", "d = new[3]; n = d.size();", 3, 0},
    DeclaredArray{"que", "d.push_back(1); d.push_back(2); n = d.size();", 2, 0},
    DeclaredArray{"aa", "d[\"a\"] = 1; d[\"b\"] = 2; n = d.num();", 2, 0},
    DeclaredArray{"arr.find with (item > 1)",
                  "d.push_back(1); n = d.size() * 10 + $bits(d[0]);", 16, 0},
    DeclaredArray{"arr.find_index with (item > 1)",
                  "d.push_back(1); n = d.size() * 100 + $bits(d[0]);", 132, 0},
};

// Where a declaration may stand: a module's items, a procedural block, a
// function and a generate block, `{0}` the declaration and `{1}` the probe.
constexpr std::array kDeclarationPlaces = {
    "  {0}\n  initial begin {1} end\n",
    "  initial begin {0} {1} end\n",
    "  function automatic void f(); {0} {1} endfunction\n"
    "  initial f();\n",
    "  if (1) begin : g {0} initial begin {1} end end\n",
};

// A module declaring the operands and an int n, with `declaration` and
// `probe` written at `place`, one of kDeclarationPlaces.
std::string ModuleDeclaring(std::string_view place,
                            const std::string& declaration,
                            const std::string& probe) {
  return std::format(
      "{}module t;\n{}  int n;\n{}endmodule\n", kOutsideTheModule, kOperands,
      std::vformat(place, std::make_format_args(declaration, probe)));
}

TEST(TypeOfExpressionDeclarationSim, DeclarationTakesAnUnpackedArrayType) {
  for (std::string_view place : kDeclarationPlaces) {
    for (const DeclaredArray& array : kDeclaredArrays) {
      for (bool own_dimension : {false, true}) {
        const std::string kSrc = ModuleDeclaring(
            place,
            std::format("var type({}) d{};", array.operand,
                        own_dimension ? " [3]" : ""),
            own_dimension ? "n = $size(d) * 1000 + $size(d[0]);" : array.probe);
        SCOPED_TRACE(kSrc);
        EXPECT_EQ(RunAndGet(kSrc, "n"),
                  own_dimension ? 3000 + array.initial_size : array.expected);
      }
    }
  }
}

// §6.23 with §8.4, §8.5 and §8.6: a declaration written with a type reference
// to a class handle holds a handle of the class, which `new` makes an object
// of; one to a property read through a handle is of the property's type,
// under the handle's specialization, its unpacked dimensions included; and
// one to a method's call, through a handle or a class scope, is of the
// method's return type. Each is declared, and its probe run, in a module, a
// procedural block, a function and a generate block.
struct DeclaredClassValue {
  const char* operand;
  const char* probe;
  uint64_t expected;
};

constexpr std::array kDeclaredClassValues = {
    DeclaredClassValue{"h", "d = new; d.x = 5; n = d.x;", 5},
    DeclaredClassValue{"dh", "d = new; d.z = 7; n = d.z + d.x;", 7},
    DeclaredClassValue{"p8", "d = new; n = $bits(d.w);", 8},
    DeclaredClassValue{"h.x", "d = -1; n = $bits(d) * 10 + (d < 0);", 81},
    DeclaredClassValue{"dh.z", "n = $bits(d);", 32},
    DeclaredClassValue{"h.y", "n = $size(d) * 10 + $bits(d[0]);", 24},
    DeclaredClassValue{"kh.kv", "n = $bits(d);", 16},
    DeclaredClassValue{"p8.w", "n = $bits(d);", 8},
    DeclaredClassValue{"p8i.t", "n = $bits(d);", 32},
    DeclaredClassValue{"h.f()", "d = -1; n = $bits(d) * 10 + (d < 0);", 161},
    DeclaredClassValue{"dh.vf()", "d = 1.5; n = d * 2;", 3},
    DeclaredClassValue{"h.sf()", "d = -1; n = $bits(d) * 10 + d;", 37},
    DeclaredClassValue{"C::sf()", "d = -1; n = $bits(d) * 10 + d;", 37},
    DeclaredClassValue{"pk::KC::ksf()", "n = $bits(d);", 64},
};

TEST(TypeOfExpressionDeclarationSim, DeclarationTakesAClassValuesType) {
  for (std::string_view place : kDeclarationPlaces) {
    for (const DeclaredClassValue& value : kDeclaredClassValues) {
      const std::string kSrc = ModuleDeclaring(
          place, std::format("var type({}) d;", value.operand), value.probe);
      SCOPED_TRACE(kSrc);
      EXPECT_EQ(RunAndGet(kSrc, "n"), value.expected);
    }
  }
}

}  // namespace
