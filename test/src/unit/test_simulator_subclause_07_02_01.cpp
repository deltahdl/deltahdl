#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackedStructSimulation, MsbFirstBitOrdering_ThreeFields) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] ra, rb, rc;\n"
      "  initial begin\n"
      "    s = 24'hAA_BB_CC;\n"
      "    ra = s.a;\n"
      "    rb = s.b;\n"
      "    rc = s.c;\n"
      "  end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0xAAu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_MiddleField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rb;\n"
      "  initial begin s = 24'hAA_BB_CC; rb = s.b; end\n"
      "endmodule\n",
      "rb");
  EXPECT_EQ(v, 0xBBu);
}

TEST(PackedStructSimulation, MsbFirstBitOrdering_LeastSignificantField) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] b;\n"
      "    logic [7:0] c;\n"
      "  } tri_t;\n"
      "  tri_t s;\n"
      "  logic [7:0] rc;\n"
      "  initial begin s = 24'hAA_BB_CC; rc = s.c; end\n"
      "endmodule\n",
      "rc");
  EXPECT_EQ(v, 0xCCu);
}

TEST(PackedStructSimulation, ArithmeticAdditionOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t a, b;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    a = 16'h0102;\n"
      "    b = 16'h0304;\n"
      "    z = a + b;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0406u);
}

TEST(PackedStructSimulation, BitwiseAndOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } w_t;\n"
      "  w_t x, y;\n"
      "  logic [15:0] z;\n"
      "  initial begin\n"
      "    x = 16'hFF0F;\n"
      "    y = 16'h0F0F;\n"
      "    z = x & y;\n"
      "  end\n"
      "endmodule\n",
      "z");
  EXPECT_EQ(v, 0x0F0Fu);
}

TEST(PackedStructSimulation, AssignFromConcatenation) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] rhi;\n"
      "  initial begin w = {8'hAB, 8'hCD}; rhi = w.hi; end\n"
      "endmodule\n",
      "rhi");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, PartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[15:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, SingleBitSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic msb;\n"
      "  initial begin w = 16'h8000; msb = w[15]; end\n"
      "endmodule\n",
      "msb");
  EXPECT_EQ(v, 1u);
}

TEST(PackedStructSimulation, WriteTwoStateValueToBitMember_OverwritesPriorX) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    s.b = 8'hA5;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xA5u);
}

TEST(PackedStructSimulation, BitMemberInFourStateStruct_ReadsAsTwoState) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'bxxxxxxxx_00000000;\n"
      "    r = s.b;\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0u);
}

// §7.2.1: a packed structure used as a whole behaves per its signedness. A
// 'packed signed' struct read as a single vector sign-extends when widened, so
// an all-ones 8-bit value fills the upper byte with ones.
TEST(PackedStructSimulation, SignedPackedStructWholeReadSignExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed signed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0xFFFFu);
}

// §7.2.1: unsigned is the default signedness of a packed structure, so the
// same whole-vector read zero-extends when widened. This discriminates the
// default from the explicit 'signed' case above.
TEST(PackedStructSimulation, UnsignedDefaultPackedStructWholeReadZeroExtends) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; } b_t;\n"
      "  b_t s;\n"
      "  logic [15:0] r;\n"
      "  initial begin s = 8'hFF; r = s; end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(v, 0x00FFu);
}

// §7.2.1 built from §6.11 integer data types: a packed structure whose members
// are declared with real Table 6-8 types (int, byte) packs them without gaps in
// most-significant-first order. Driven end-to-end (parse/elaborate/run), the
// first member occupies the high bits of the whole vector.
TEST(PackedStructSimulation, IntegerTypeMembersPackMsbFirst) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { int a; byte b; } m_t;\n"
      "  m_t m;\n"
      "  logic [31:0] ra;\n"
      "  initial begin m = 40'h1122334455; ra = m.a; end\n"
      "endmodule\n",
      "ra");
  EXPECT_EQ(v, 0x11223344u);
}

// §7.2.1: bits of a packed structure may be selected as if it were a packed
// array [n-1:0]. This exercises the indexed part-select form ([base+:width]),
// distinct from the fixed [msb:lsb] and single-bit select forms.
TEST(PackedStructSimulation, IndexedPartSelectOnPackedStruct) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [7:0] top_byte;\n"
      "  initial begin w = 16'hABCD; top_byte = w[8+:8]; end\n"
      "endmodule\n",
      "top_byte");
  EXPECT_EQ(v, 0xABu);
}

TEST(PackedStructSimulation, MemberWriteUpdatesWholeVector) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } w_t;\n"
      "  w_t w;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    w = 16'h0000;\n"
      "    w.hi = 8'hAB;\n"
      "    result = w;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xAB00u);
}

// §7.2.1 makes a member of a packed structure a named window on the bits of one
// variable -- the members "are packed together in memory without gaps" -- and
// §10.4.2 asks of a nonblocking target only that "variable_lvalue is a data
// type that is valid for a procedural assignment statement", which A.8.5 opens
// with the dotted member path. So `s.b <= 8'hA5` has to reach the same eight
// bits that WriteTwoStateValueToBitMember_OverwritesPriorX above reaches with
// `=`, the two forms differing only in when the write lands.
//
// They differed in whether it landed at all. ScheduleNonblockingAssign resolved
// a member-access target through ResolveLhsVariable, which rebuilds the dotted
// name and asks ctx.FindVariable; a packed member is a bit field inside `s` and
// no variable is registered under "s.b", so the lookup answered null and the
// function returned having acquired no update event, performed no write and
// reported no diagnostic. `r` read 8'h00.
//
// The whole structure is asserted beside `r` because `r` alone cannot say which
// bits the write reached: a write that landed on the low half would leave `s`
// at 16'h00A5 while `r`, reading the member back through the same wrong window,
// could still answer 8'hA5. `s` at 16'hA500 is the member in its declared
// place, the high byte, with the four-state half below it untouched. The #1 is
// required rather than decorative -- a nonblocking assignment takes effect in
// the update region, so a read at time 0 answers the old value however the
// scheduling behaves.
TEST(PackedStructSimulation, NonblockingWriteToBitMemberReachesThatMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { bit [7:0] b; logic [7:0] l; } mixed_t;\n"
      "  mixed_t s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 16'h0000;\n"
      "    s.b <= 8'hA5;\n"
      "    #1 r = s.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r", 0xA5u}, {"s", 0xA500u}});
}

// §7.2.1 writes a member select as `struct_variable.member` and makes no part
// of the selection depend on what the structure is stored in. A class property
// declared with a packed struct type holds the whole structure in one value
// (§6.8/§8.3), so `c.p.b` selects a run of that value's bits exactly as `s.b`
// selects a run of a module variable's.
//
// The member write went to a property keyed by the whole dotted path -- a name
// the class never declared -- so `c.p` kept the 16'hAABB it was assigned and
// only a read written the same way could see the 8'h05. Reading the property
// itself is what tells them apart.
TEST(PackedStructSimulation, MemberWriteThroughAClassPropertyLandsInTheValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [15:0] r1;\n"
      "  logic [7:0] r2;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    c.p.b = 8'h05;\n"
      "    r1 = c.p;\n"
      "    r2 = c.p.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r1", 0x05BBu}, {"r2", 0x05u}});
}

// The other half: a member read after a whole-property write. The value is in
// the property, so both members are read out of it -- the high member is 8'hAA
// and the low one 8'hBB. The read answered from the flattened key instead,
// which no write had created, and ClassObject::GetProperty answers a known zero
// for a key it does not hold.
TEST(PackedStructSimulation, MemberReadThroughAClassPropertyTakesItsBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [7:0] rb, rl;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    rb = c.p.b;\n"
      "    rl = c.p.l;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"rb", 0xAAu}, {"rl", 0xBBu}});
}

// A member write reaches its own member and no other, which is what says the
// window is the one the layout gives rather than the whole property: the low
// member takes 8'h07 and the high member keeps the 8'hAA it was assigned.
TEST(PackedStructSimulation, MemberWriteThroughAPropertyLeavesTheOtherMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] b; logic [7:0] l; } pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  logic [15:0] r1;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    c.p = 16'hAABB;\n"
      "    c.p.l = 8'h07;\n"
      "    r1 = c.p;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors) << "source reported an elaboration error";
  LowerRunAndCheck(f, design, {{"r1", 0xAA07u}});
}

// §7.2.1 with §23.9: a member of a packed structure declared in an
// instantiated module is a window of that instance's own vector. The child
// writes 8'hA5 into opcode and 24'h123456 into imm, and the top reads the
// whole of `m.s` as 32'hA5123456. Both writes went nowhere -- the target was
// resolved by asking the layout table for bare `s`, while the instance's
// layout is keyed "m.s" -- so the whole read 0 and both members read 0. The
// values tell a landed write from a misplaced one: opcode's high bit is set,
// so a write at bit 0 instead of bit 24 reads 0x000000A5 for the whole, and
// imm differs in every byte from opcode.
TEST(PackedStructSimulation, ChildInstanceMemberWriteLandsInItsWindow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t s;\n"
      "  int op, im;\n"
      "  initial begin\n"
      "    s.opcode = 8'hA5;\n"
      "    s.imm = 24'h123456;\n"
      "    op = s.opcode;\n"
      "    im = s.imm;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "  int whole;\n"
      "  initial #1 whole = m.s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* whole = f.ctx.FindVariable("whole");
  auto* op = f.ctx.FindVariable("m.op");
  auto* im = f.ctx.FindVariable("m.im");
  ASSERT_NE(whole, nullptr);
  ASSERT_NE(op, nullptr);
  ASSERT_NE(im, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0xA5123456u);
  EXPECT_EQ(op->value.ToUint64(), 0xA5u);
  EXPECT_EQ(im->value.ToUint64(), 0x123456u);
}

// §10.9.2: a structure assignment pattern keyed by member name places each
// value in the member it names, whatever order the keys are written in. The
// child assigns `'{imm: 24'h0F1E2D, opcode: 8'h5A}` and the top reads the
// whole of `m.s` as 32'h5A0F1E2D. With the layout looked up by bare `s`
// inside instance `m`, no layout was found and the pattern fell back to a
// concatenation of the values in written order, 32'h0F1E2D5A, with opcode
// reading 0x0F; the keys are written in the reverse of the declaration order
// so that fallback and the keyed placement cannot agree.
TEST(PackedStructSimulation, ChildInstanceKeyedPatternPlacesEachMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef struct packed { logic [7:0] opcode; logic [23:0] imm; } "
      "instruction_t;\n"
      "  instruction_t s;\n"
      "  int op;\n"
      "  initial begin\n"
      "    s = '{imm: 24'h0F1E2D, opcode: 8'h5A};\n"
      "    op = s.opcode;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "  int whole;\n"
      "  initial #1 whole = m.s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* whole = f.ctx.FindVariable("whole");
  auto* op = f.ctx.FindVariable("m.op");
  ASSERT_NE(whole, nullptr);
  ASSERT_NE(op, nullptr);
  EXPECT_EQ(whole->value.ToUint64(), 0x5A0F1E2Du);
  EXPECT_EQ(op->value.ToUint64(), 0x5Au);
}

// §7.2.1 makes a member a window on the structure's bits, and §10.7 has an
// assignment write the whole right-hand value into the target, so a 96-bit
// member takes all 96 bits of its value. `big` sits at bits [103:8] of `s` and
// `low8` at [7:0]: word 0 of `s` is big's low 56 bits over 0xA5, and word 1 the
// 40 bits above, 0x0123456789; read back as a member, `w` holds the literal
// whole. A write that carried one word of the value would leave word 1 of `s`
// at 0x89 and `w`'s high word at 0. These pins were written when the stream of
// `s` read that word as 0x89 (test_simulator_subclause_11_04_14_01.cpp) and
// the write was suspected; it was the stream's 64-bit carrier, and the deposit
// this pins was whole all along.
TEST(PackedStructSimulation, WideMemberWriteLandsEveryWordOfItsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  logic [95:0] w;\n"
      "  initial begin\n"
      "    s.big = 96'h0123_4567_89AB_CDEF_0F1E_2D3C;\n"
      "    s.low8 = 8'hA5;\n"
      "    w = s.big;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0F1E2D3CA5u);
  EXPECT_EQ(var->value.words[1].aval, 0x0123456789u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  ASSERT_EQ(w->value.nwords, 2u);
  EXPECT_EQ(w->value.words[0].aval, 0x89ABCDEF0F1E2D3Cu);
  EXPECT_EQ(w->value.words[1].aval, 0x01234567u);
}

// §7.3.1: the members of a packed union share the union's storage, each a
// window on all of it, so 96 bits written through `w` are the 96 bits read
// through `v`, high word included: 0xFEDCBA98 above 0x765432100F0FA5A5. A write
// that carried one word would leave the high word x, the union's initial value.
TEST(PackedStructSimulation, WideUnionMemberWriteReadsBackThroughTheOther) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  union packed { logic [95:0] w; logic [95:0] v; } u;\n"
      "  logic [95:0] rv;\n"
      "  initial begin\n"
      "    u.w = 96'hFEDC_BA98_7654_3210_0F0F_A5A5;\n"
      "    rv = u.v;\n"
      "  end\n"
      "endmodule\n",
      f, "rv");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.words[0].aval, 0x765432100F0FA5A5u);
  EXPECT_EQ(var->value.words[1].aval, 0xFEDCBA98u);
}

// §7.2.1 has a structure with a 4-state member be a 4-state vector, and §6.3.1
// lets any bit of a logic member be x, so x digits above bit 64 of the value
// land as x above bit 72 of `s` (big's offset is 8): word 1 of `s` carries
// aval and bval 1 in bits [39:8] and the known 0x89 in [7:0]. A deposit that
// moved the aval plane alone would read those bits as a known 1.
TEST(PackedStructSimulation, WideMemberWriteKeepsXAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  initial begin\n"
      "    s.big = 96'hxxxx_xxxx_89AB_CDEF_0F1E_2D3C;\n"
      "    s.low8 = 8'hA5;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0xABCDEF0F1E2D3CA5u);
  EXPECT_EQ(var->value.words[0].bval, 0u);
  EXPECT_EQ(var->value.words[1].aval, 0xFFFFFFFF89u);
  EXPECT_EQ(var->value.words[1].bval, 0xFFFFFFFF00u);
}

// §10.4.2: a nonblocking assignment to the member lands the whole 96 bits in
// the update region, so after #1 `s` holds them at the member's offset, its
// own values so the blocking test above is not mistaken for this one.
TEST(PackedStructSimulation, WideMemberNonblockingWriteLandsEveryWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  struct packed { logic [95:0] big; logic [7:0] low8; } s;\n"
      "  logic [95:0] w;\n"
      "  initial begin\n"
      "    s.big <= 96'hFEDC_BA98_7654_3210_0F0F_A5A5;\n"
      "    s.low8 <= 8'h3C;\n"
      "    #1 w = s.big;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  ASSERT_EQ(var->value.nwords, 2u);
  EXPECT_EQ(var->value.words[0].aval, 0x5432100F0FA5A53Cu);
  EXPECT_EQ(var->value.words[1].aval, 0xFEDCBA9876u);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.words[1].aval, 0xFEDCBA98u);
}

}  // namespace
