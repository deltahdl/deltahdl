#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context_types.h"

using namespace delta;

static void VerifyStructField(const StructFieldInfo& field,
                              const char* expected_name,
                              uint32_t expected_offset, uint32_t expected_width,
                              size_t index) {
  EXPECT_EQ(field.name, expected_name) << "field " << index;
  EXPECT_EQ(field.bit_offset, expected_offset) << "field " << index;
  EXPECT_EQ(field.width, expected_width) << "field " << index;
}

namespace {

TEST(StructType, RegisterAndFind_Metadata) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});
  info.fields.push_back({"y", 0, 8});

  f.ctx.RegisterStructType("point_t", info);
  auto* found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->type_name, "point_t");
  EXPECT_TRUE(found->is_packed);
  EXPECT_EQ(found->total_width, 16u);
  ASSERT_EQ(found->fields.size(), 2u);
}

TEST(StructType, RegisterAndFind_Fields) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});
  info.fields.push_back({"y", 0, 8});

  f.ctx.RegisterStructType("point_t", info);
  auto* found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  ASSERT_EQ(found->fields.size(), 2u);

  VerifyStructField(found->fields[0], "x", 8, 8, 0);
  VerifyStructField(found->fields[1], "y", 0, 8, 1);
}

TEST(StructType, FindNonexistent) {
  SimFixture f;
  EXPECT_EQ(f.ctx.FindStructType("no_such_type"), nullptr);
}

TEST(StructType, SetVariableStructType) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "color_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8});
  info.fields.push_back({"g", 8, 8});
  info.fields.push_back({"b", 0, 8});
  f.ctx.RegisterStructType("color_t", info);

  f.ctx.CreateVariable("pixel", 24);
  f.ctx.SetVariableStructType("pixel", "color_t");

  auto* type = f.ctx.GetVariableStructType("pixel");
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->type_name, "color_t");
  EXPECT_EQ(type->fields.size(), 3u);
}

TEST(StructType, GetVariableStructTypeUnknown) {
  SimFixture f;
  EXPECT_EQ(f.ctx.GetVariableStructType("nonexistent"), nullptr);
}

TEST(StructType, FieldTypeKindPreserved) {
  SimFixture f;
  StructTypeInfo info;
  info.type_name = "typed_s";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});
  f.ctx.RegisterStructType("typed_s", info);
  auto* found = f.ctx.FindStructType("typed_s");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->fields[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(found->fields[1].type_kind, DataTypeKind::kByte);
}

TEST(StructMemberAccess, MemberAccessBasic) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("s.x", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 99);

  auto* acc = f.arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = MakeId(f.arena, "s");
  acc->rhs = MakeId(f.arena, "x");

  auto result = EvalExpr(acc, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

// §7.2 with §6.18: a member declared through a typedef holds the typedef's
// type -- `ab_e e` of `typedef enum logic [1:0] {A=1, B=2} ab_e` two bits,
// `six_t w` of `typedef logic [5:0] six_t` six -- in an unpacked struct and a
// packed one alike, as $bits of the struct already counted them. The run-time
// layout gave each one bit, so B and 6'h2a read back as 0.
TEST(StructType, MembersDeclaredThroughTypedefsHoldTheirWidth) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum logic [1:0] {A=1, B=2} ab_e;\n"
      "  typedef logic [5:0] six_t;\n"
      "  typedef struct {ab_e e; six_t w; int n;} s_t;\n"
      "  typedef struct packed {ab_e e; six_t w;} ps_t;\n"
      "  s_t s = '{B, 6'h2a, 3};\n"
      "  ps_t ps = '{B, 6'h2a};\n"
      "  initial $display(\"%0d %h %0d %0d %h %h %p\", s.e, s.w, s.n, ps.e, "
      "ps.w,\n"
      "                   ps, s);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 2a 3 2 2a aa '{e:B, w:42, n:3}\n");
}

// §7.2.1 with §6.11: a member reads as the type it is declared with, so a
// shortint and a byte member of an unpacked struct hold -2 and -3, a
// `logic signed [3:0]` member -1, and a `bit [3:0]` member 15; each compares
// below zero exactly when its type is signed.
TEST(StructType, SignedMembersOfAnUnpackedStructReadSigned) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {\n"
      "    shortint address; byte c; logic signed [3:0] s; bit [3:0] u;\n"
      "  } Plain;\n"
      "  Plain pl;\n"
      "  initial begin\n"
      "    pl.address = -2;\n"
      "    pl.c = -3;\n"
      "    pl.s = -1;\n"
      "    pl.u = -1;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", pl.address, pl.c, pl.s, "
      "pl.u, pl.c < 0, pl.u < 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-2 -3 -1 15 1 0\n");
}

// §7.2 and §7.3 with §6.21: a structure or union declared in an initial block
// or a static task has storage like any variable, so a whole assignment, a
// member write and a member read all reach it -- st holds 9 and 1, the union
// reads 16'h1234 through either member, the inline packed struct's x holds 5,
// and the task's local 7. Bound to no layout, each member read 0 or x.
TEST(StructType, AggregateLocalsOfAStaticBlockAndTaskHoldTheirValues) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {int x; byte y;} s_t;\n"
      "  typedef union packed {bit [15:0] w; bit [1:0][7:0] b;} u_t;\n"
      "  int bx, by, uw, ub, px, tx;\n"
      "  task tk; s_t ts; ts.x = 7; tx = ts.x; endtask\n"
      "  initial begin\n"
      "    s_t st;\n"
      "    u_t u;\n"
      "    struct packed {int x; byte y;} ps;\n"
      "    st = '{8, 1};\n"
      "    st.x = st.x + 1;\n"
      "    bx = st.x; by = st.y;\n"
      "    u.w = 16'h1234;\n"
      "    uw = u.w; ub = u.b;\n"
      "    ps.x = 5;\n"
      "    px = ps.x;\n"
      "    tk();\n"
      "    $display(\"%0d %0d %h %h %0d %0d\", bx, by, uw, ub, px, tx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9 1 00001234 00001234 5 7\n");
}

// §7.2 with §7.4.2: an unpacked array member of an unpacked struct holds each
// of its elements, so m.v[1] and m.v[3] keep 20 and 40 beside n's 5, the
// struct is 32 + 4*32 = 160 bits, and a member after an array member keeps
// its own value. Laid out as one element, the writes landed in n or nowhere.
TEST(StructType, UnpackedArrayMemberHoldsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int n; int v[4]; } rec_t;\n"
      "  typedef struct { int v[2]; byte tail; } t_t;\n"
      "  rec_t m;\n"
      "  t_t t2;\n"
      "  initial begin\n"
      "    m.v[1] = 20; m.v[3] = 40; m.n = 5;\n"
      "    t2.v[0] = 7; t2.v[1] = 9; t2.tail = 3;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", m.v[1], m.v[3], m.n,\n"
      "             $bits(m), t2.v[0], t2.v[1], t2.tail);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20 40 5 160 7 9 3\n");
}

// §7.2 with §7.4.4: a member declared with an unpacked-array typedef has the
// typedef's dimensions, `a_t m1;` under `typedef bit a_t [3:0];` being four
// bits as `bit m1 [3:0]` is, so the struct is 12 bits, m1[3] keeps the 1
// written to it and the byte after m1 keeps its own value.
TEST(StructType, MemberDeclaredWithAnArrayTypedefHoldsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit a_t [3:0];\n"
      "  typedef struct { a_t m1; byte tail; } st;\n"
      "  st s;\n"
      "  initial begin\n"
      "    s.m1[3] = 1; s.tail = 8'h5A;\n"
      "    $display(\"%0d %0d %0d %h\", $bits(s), $bits(s.m1), s.m1[3], "
      "s.tail);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "12 4 1 5a\n");
}

// §10.9.2 with §7.2 and §7.4.2: a nested pattern for an unpacked array member
// gives each element its value, left to right, each as wide as the element:
// `'{2, 3, 4, 5}` fills `byte data[4]` in a declaration initializer and in an
// assignment, and `'{1, 2, 3, 4}` fills `int v[4]`. Concatenated at their own
// widths, the byte member kept only the last value.
TEST(StructType, NestedPatternFillsAnArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int addr; int crc; byte data[4]; } packet1;\n"
      "  typedef struct { int n; int v[4]; } rec_t;\n"
      "  packet1 pi = '{1, 2, '{2, 3, 4, 5}};\n"
      "  rec_t l;\n"
      "  packet1 p2;\n"
      "  initial begin\n"
      "    l = '{5, '{1, 2, 3, 4}};\n"
      "    p2 = '{7, 8, '{9, 10, 11, 12}};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", pi.data[0], pi.data[3],\n"
      "             l.v[0], l.v[3], p2.data[0], p2.data[3], p2.crc);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 5 1 4 9 12 8\n");
}

// §7.2.2 with §10.9.1: a member default gives a variable with no initializer
// its value, and a replicated default pattern for an unpacked array member,
// `byte data[4] = '{4{1}}`, gives every element 1, beside addr's default 6.
// Evaluated as one value, it reached the last element alone.
TEST(StructType, ArrayMemberDefaultFillsEachElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {\n"
      "    int addr = 6; int crc; byte data[4] = '{4{1}};\n"
      "  } packet1;\n"
      "  packet1 p1;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", p1.addr, p1.data[0],\n"
      "                   p1.data[1], p1.data[2], p1.data[3]);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "6 1 1 1 1\n");
}

// §12.7.3 with §7.2 and §7.4.2: foreach over an unpacked array member iterates
// its elements -- a module variable's `m.v`, a property's `r.v` bare in a
// method, and `h.r.v` through a handle -- so the four elements written with
// (i+1)*10 and (i+1)*100 sum to 100 and 1000. Found no array, each loop ran
// no iteration.
TEST(StructType, ForeachOverAnArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int n; int v[4]; } rec_t;\n"
      "  class C;\n"
      "    rec_t r;\n"
      "    function void fill(); foreach (r.v[i]) r.v[i] = (i+1)*100; "
      "endfunction\n"
      "    function int total();\n"
      "      int s = 0;\n"
      "      foreach (r.v[i]) s += r.v[i];\n"
      "      return s;\n"
      "    endfunction\n"
      "  endclass\n"
      "  rec_t m;\n"
      "  C h;\n"
      "  int s, hs;\n"
      "  initial begin\n"
      "    foreach (m.v[i]) m.v[i] = (i+1)*10;\n"
      "    s = 0; foreach (m.v[i]) s += m.v[i];\n"
      "    h = new; h.fill();\n"
      "    hs = 0; foreach (h.r.v[i]) hs += h.r.v[i];\n"
      "    $display(\"%0d %0d %0d\", s, h.total(), hs);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "100 1000 1000\n");
}

// §7.12 with §7.2 and §7.4.2: an unpacked array member of a structure is an
// unpacked array, so after `r.v = '{4, 5, 6}` its size() is 3 and its sum()
// 15, while the member beside it keeps its own value. Named no array of its
// own, the member answered 0 to both.
TEST(StructType, ArrayMethodsOnAnArrayMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct { int n; int v[3]; } rec_t;\n"
      "  rec_t r;\n"
      "  initial begin\n"
      "    r.v = '{4, 5, 6};\n"
      "    r.n = 1;\n"
      "    $display(\"%0d %0d %0d %0d\", r.v.sum(), r.v.size(), r.v.product(), "
      "r.n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 3 120 1\n");
}

// §7.2 with §6.16: a string member of an unpacked structure is a string
// variable, holding whatever string is written to it at whatever length: "d"
// reads back as "d", and a 28-character string reads back whole, its len()
// 28, beside an enum member that keeps its own value.
TEST(StructType, AStringMemberHoldsTheStringWrittenToIt) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum {ON, OFF} switch_e;\n"
      "  typedef struct {switch_e sw; string s;} pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.sw = OFF;\n"
      "    p.s = \"d\";\n"
      "    $display(\"[%s] %0d\", p.s, p.sw);\n"
      "    p.s = \"hello world, a longer string\";\n"
      "    $display(\"[%s] %0d\", p.s, p.s.len());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[d] 1\n[hello world, a longer string] 28\n");
}

// §7.2 with §10.9.2: an assignment pattern gives a string member its string,
// positionally or by the member's name, and a copy of the whole structure,
// through an associative array's element among others, carries the string
// with it; a member never written holds the empty string.
TEST(StructType, AStringMemberTravelsWithItsStructure) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  pair_t p, q, r, blank;\n"
      "  pair_t va[int];\n"
      "  initial begin\n"
      "    q = '{7, \"hello\"};\n"
      "    va[20] = q;\n"
      "    p = va[20];\n"
      "    r = '{s: \"x\", n: 3};\n"
      "    $display(\"[%s] %0d [%s] %0d [%s]\", p.s, p.n, r.s, r.n, blank.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[hello] 7 [x] 3 []\n");
}

// §21.2.1.6 with §7.2: %p prints a structure's string member as its quoted
// string.
TEST(StructType, PercentPPrintsAStringMemberQuoted) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef enum {ON, OFF} switch_e;\n"
      "  typedef struct {switch_e sw; string s;} pair_t;\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    p.sw = OFF;\n"
      "    p.s = \"d\";\n"
      "    $display(\"%p\", p);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "'{sw:OFF, s:\"d\"}\n");
}

// §11.4.5 with §7.2: structures whose string members hold equal strings,
// written separately, compare equal, and ones whose strings differ do not.
TEST(StructType, StructuresWithEqualStringMembersCompareEqual) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  pair_t p, q;\n"
      "  initial begin\n"
      "    p = '{1, \"ab\"};\n"
      "    q.n = 1;\n"
      "    q.s = {\"a\", \"b\"};\n"
      "    $display(\"%0d\", p == q);\n"
      "    q.s = \"ac\";\n"
      "    $display(\"%0d\", p == q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n0\n");
}

// §7.2 with §6.16: a structure's string member holds its string wherever the
// structure is kept -- a class property, an element of an associative array,
// a queue or a fixed-size array -- whether the member is written in place and
// the structure then copied out, or the structure copied in whole and the
// member then read in place; and a function returning the structure returns
// its string with it.
TEST(StructType, AStringMemberHoldsItsStringWhereverTheStructureIsKept) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  class C;\n"
      "    pair_t p;\n"
      "  endclass\n"
      "  function automatic pair_t mk();\n"
      "    pair_t r;\n"
      "    r.s = \"from a function\";\n"
      "    return r;\n"
      "  endfunction\n"
      "  C c;\n"
      "  pair_t va[int];\n"
      "  pair_t q[$];\n"
      "  pair_t arr[2];\n"
      "  pair_t tmp;\n"
      "  initial begin\n"
      "    c = new;\n"
      "    c.p.s = \"in a class property\";\n"
      "    va[1].s = \"in an associative element\";\n"
      "    q.push_back(tmp);\n"
      "    q[0].s = \"in a queue element\";\n"
      "    arr[1].s = \"in an array element\";\n"
      "    tmp = c.p; $display(\"[%s]\", tmp.s);\n"
      "    tmp = va[1]; $display(\"[%s]\", tmp.s);\n"
      "    tmp = q[0]; $display(\"[%s]\", tmp.s);\n"
      "    tmp = arr[1]; $display(\"[%s]\", tmp.s);\n"
      "    tmp.s = \"copied in whole\";\n"
      "    c.p = tmp; va[2] = tmp; q.push_back(tmp); arr[0] = tmp;\n"
      "    $display(\"[%s] [%s] [%s] [%s]\", c.p.s, va[2].s, q[1].s, "
      "arr[0].s);\n"
      "    $display(\"[%s]\", mk().s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "[in a class property]\n[in an associative element]\n"
            "[in a queue element]\n[in an array element]\n"
            "[copied in whole] [copied in whole] [copied in whole] "
            "[copied in whole]\n[from a function]\n");
}

// §7.2 with §6.8: each member of an unpacked structure is a variable of its
// type, so one declared without an initializer starts with its 4-state
// members at x, its 2-state members at 0 and its string member empty, and an
// assignment to the whole structure keeps a 4-state member's x and z bits.
TEST(StructType, UnpackedMembersStartAtTheirTypesDefaults) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef struct {logic [3:0] l; int i; string s;} lis_t;\n"
      "  typedef struct {logic [3:0] l; logic k;} ll_t;\n"
      "  lis_t a, b;\n"
      "  ll_t c;\n"
      "  initial begin\n"
      "    $display(\"%b %0d [%s] %b %b\", a.l, a.i, a.s, c.l, c.k);\n"
      "    b = '{4'bz01x, 5, \"s\"};\n"
      "    $display(\"%b %0d [%s]\", b.l, b.i, b.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xxxx 0 [] xxxx x\nz01x 5 [s]\n");
}

// §7.2: a member of an unpacked structure may be a dynamic array, sized by
// new[] and written and read element by element through the member.
TEST(UnpackedStructDynamicMember, ADynamicMemberIsSizedWrittenAndRead) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a; byte data[]; } h_t;\n"
      "module t;\n"
      "  h_t w;\n"
      "  initial begin\n"
      "    w.data = new[3];\n"
      "    w.data[1] = 9;\n"
      "    w.a = 5;\n"
      "    $display(\"%0d %0d %0d %0d\", w.data.size(), w.data[1], w.data[0],\n"
      "             w.a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 9 0 5\n");
}

// §7.2.2: a dynamic member's declared initial value is every variable's of
// the structure, a module's and a class property's alike.
TEST(UnpackedStructDynamicMember, ADynamicMembersInitializerIsTaken) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a = 7; byte data[] = {1, 2, 3, 4}; } h_t;\n"
      "class P; h_t h; endclass\n"
      "module t;\n"
      "  h_t m;\n"
      "  initial begin\n"
      "    static P p = new;\n"
      "    $display(\"%0d %0d %0d | %0d %0d %0d\", m.a, m.data.size(),\n"
      "             m.data[3], p.h.a, p.h.data.size(), p.h.data[2]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 4 4 | 7 4 3\n");
}

// §7.2: assigning a structure assigns each of its members, so the copy
// holds its own dynamic member, which a later write to the source leaves.
TEST(UnpackedStructDynamicMember, AStructAssignmentCopiesTheDynamicMember) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { byte data[]; } h_t;\n"
      "module t;\n"
      "  h_t x, y;\n"
      "  initial begin\n"
      "    x.data = new[2];\n"
      "    x.data[0] = 4;\n"
      "    y = x;\n"
      "    x.data[0] = 6;\n"
      "    $display(\"%0d %0d %0d\", y.data.size(), y.data[0], x.data[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 4 6\n");
}

// §7.2 with §7.5: a dynamic member never written holds no element, and the
// queue methods a dynamic array shares grow it, a copy taken before the
// growth keeping the elements it was taken with.
TEST(UnpackedStructDynamicMember, AnUnwrittenMemberIsEmptyAndGrowsByMethod) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { byte data[]; } h_t;\n"
      "module t;\n"
      "  h_t e, c;\n"
      "  initial begin\n"
      "    $display(\"%0d\", e.data.size());\n"
      "    e.data = new[1];\n"
      "    c = e;\n"
      "    e.data.push_back(4);\n"
      "    $display(\"%0d %0d %0d\", e.data.size(), e.data[1], "
      "c.data.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n2 4 1\n");
}

}  // namespace
