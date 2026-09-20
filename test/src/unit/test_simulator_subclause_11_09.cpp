#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(TaggedUnionEval, TaggedUnionNoTagSetAccessesNormally) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "simple_u";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"x", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("simple_u", uinfo);

  MakeVar(f, "v", 8, 0xFF);
  f.ctx.SetVariableStructType("v", "simple_u");

  auto* access_x = f.arena.Create<Expr>();
  access_x->kind = ExprKind::kMemberAccess;
  access_x->lhs = MakeId(f.arena, "v");
  access_x->rhs = MakeId(f.arena, "x");
  auto result_x = EvalExpr(access_x, f.ctx, f.arena);
  EXPECT_EQ(result_x.ToUint64(), 0xFFu);
}

TEST(TaggedUnionEval, TaggedExprWithValue) {
  SimFixture f;

  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Valid";
  tagged->rhs = member;
  tagged->lhs = MakeInt(f.arena, 42);
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

TEST(TaggedUnionEval, TaggedExprVoidMember) {
  SimFixture f;

  auto* tagged = f.arena.Create<Expr>();
  tagged->kind = ExprKind::kTagged;
  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = "Invalid";
  tagged->rhs = member;
  tagged->lhs = nullptr;
  auto result = EvalExpr(tagged, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(TaggedUnionEval, TaggedAssignSetsTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 7;\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 7u);
}

TEST(TaggedUnionEval, TaggedAssignOverwriteAndRead) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int X; int Y; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged X 100;\n"
      "    u = tagged Y 200;\n"
      "    result = u.Y;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 200u);
}

// A write through dot notation whose member name matches the current tag
// updates the union storage in place and raises no diagnostic.
TEST(TaggedUnionEval, MatchingMemberWriteUpdatesValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_wr_ok";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_wr_ok", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x00);
  f.ctx.SetVariableStructType("u", "u_wr_ok");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "a");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x5A);

  WriteStructField(lhs, rhs_val, f.ctx);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(var->value.ToUint64(), 0x5Au);
}

// A write whose member name does not match the current tag must surface a
// run-time error diagnostic and leave the union storage unchanged.
TEST(TaggedUnionEval, MismatchedWriteEmitsDiagnosticAndKeepsValue) {
  SimFixture f;

  StructTypeInfo uinfo;
  uinfo.type_name = "u_diag_w";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"a", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_diag_w", uinfo);

  auto* var = MakeVar(f, "u", 8, 0x33);
  f.ctx.SetVariableStructType("u", "u_diag_w");
  f.ctx.SetVariableTag("u", "a");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "u");
  lhs->rhs = MakeId(f.arena, "b");
  auto rhs_val = MakeLogic4VecVal(f.arena, 8, 0x77);

  EXPECT_FALSE(f.diag.HasErrors());
  WriteStructField(lhs, rhs_val, f.ctx);
  // The target expression is built in the arena rather than parsed, so the
  // report carries the default location of line 0.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: assigning member", 0, "11.9"));
  EXPECT_EQ(var->value.ToUint64(), 0x33u);
}

TEST(TaggedUnionEval, VoidMemberThenValueMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o;\n"
      "  int result;\n"
      "  initial begin\n"
      "    o = tagged None;\n"
      "    o = tagged Some 77;\n"
      "    result = o.Some;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 77u);
}

// §11.9: a variable of tagged union type can be initialized with a tagged union
// expression whose member value is a legal initializer for the member type. The
// declaration initializer (a syntactic position distinct from a procedural
// assignment) establishes the member value, read back through dot notation.
TEST(TaggedUnionEval, DeclarationInitializerHoldsMemberValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.A;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// §11.9: initializing a tagged-union variable with `tagged A ...` also
// establishes its active tag (like a procedural `u = tagged A ...`), so a later
// read of a different member is inconsistent with the current tag and must
// raise a run-time error. Drives the initializer tag-set path end to end.
TEST(TaggedUnionEval, DeclarationInitializerSetsTagForMemberCheck) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int result;\n"
      "  initial result = u.B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 5, "11.9"));
}

// §11.9: members of a tagged union are read using the usual dot notation and
// the read shall be consistent with the current tag. After a real procedural
// `u = tagged A ...` sets the tag, reading member B is inconsistent and raises
// a run-time error (tag produced by real source, not a hand-set fixture tag).
TEST(TaggedUnionEval, ProceduralAssignThenMismatchedReadErrors) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 5;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 7, "11.9"));
}

// §11.9: an uninitialized variable of tagged union type is undefined, which
// includes its tag bits — no member is current. Built from a real declaration
// with no initializer and observed after a run: the variable exists but carries
// no active tag.
TEST(TaggedUnionEval, UninitializedTaggedUnionHasNoActiveTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  ASSERT_NE(f.ctx.FindVariable("u"), nullptr);
  EXPECT_TRUE(f.ctx.GetVariableTag("u").empty());
}

// §11.9: the type of a tagged union expression may be supplied by a cast rather
// than by an assignment target. `U'(tagged A ...)` names the union type, so the
// tagged expression is evaluated in that context and yields its member value.
TEST(TaggedUnionEval, CastContextTaggedExprEvaluates) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = U'(tagged A 9);\n"
      "    result = u.A;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §11.9 + dependency §10.9.2: the member value of a tagged expression may be a
// structure assignment pattern. Built from real source (a struct-typed union
// member assigned `tagged Add '{...}`) and driven end to end — the positional
// pattern is packed against the member's own field layout, so reading a nested
// field back yields the value placed there rather than a mis-concatenated bit
// range.
TEST(TaggedUnionEval, TaggedMemberValueFromStructAssignmentPattern) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef struct packed { bit [4:0] reg1; bit [4:0] reg2;\n"
      "                          bit [4:0] regd; } add_t;\n"
      "  typedef union tagged { add_t Add; bit [14:0] Jmp; } Instr;\n"
      "  Instr i1;\n"
      "  int result;\n"
      "  initial begin\n"
      "    i1 = tagged Add '{5, 9, 3};\n"
      "    result = i1.Add.reg2;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 9u);
}

// §11.9: a declaration initializer may use the void-member form of a tagged
// expression (no member value primary). It still establishes the active tag, so
// a later read of a different member is inconsistent with that tag and raises a
// run-time error.
TEST(TaggedUnionEval, VoidMemberDeclarationInitializerSetsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void None; int Some; } Opt;\n"
      "  Opt o = tagged None;\n"
      "  int result;\n"
      "  initial result = o.Some;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 5, "11.9"));
}

// §11.9: an attempt to read a value whose type is inconsistent with the
// current tag is a run-time error, and the report names §11.9.
TEST(TaggedUnionEval, MismatchedReadNames11_9) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { int P; int Q; } TU;\n"
      "  TU u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged P 7;\n"
      "    result = u.Q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 7, "11.9"));
}

// §11.9: the same sentence covers an assignment whose type is inconsistent
// with the tag, which is reported on the write path and names §11.9 too.
TEST(TaggedUnionEval, MismatchedWriteNames11_9) {
  SimFixture f;
  StructTypeInfo uinfo;
  uinfo.type_name = "u_sub_w";
  uinfo.is_union = true;
  uinfo.is_packed = true;
  uinfo.total_width = 8;
  uinfo.fields.push_back({"p", 0, 8, DataTypeKind::kLogic});
  uinfo.fields.push_back({"q", 0, 8, DataTypeKind::kLogic});
  f.ctx.RegisterStructType("u_sub_w", uinfo);

  MakeVar(f, "us", 8, 0x11);
  f.ctx.SetVariableStructType("us", "u_sub_w");
  f.ctx.SetVariableTag("us", "p");

  auto* lhs = f.arena.Create<Expr>();
  lhs->kind = ExprKind::kMemberAccess;
  lhs->lhs = MakeId(f.arena, "us");
  lhs->rhs = MakeId(f.arena, "q");
  WriteStructField(lhs, MakeLogic4VecVal(f.arena, 8, 0x22), f.ctx);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: assigning member", 0, "11.9"));
}

// §11.9 with §23.9: a tagged-union variable declared with an initializer
// inside an instantiated module resolves within that instance, so the tag
// its initializer sets governs every later member access of it there. The
// declaration form recorded the tag under the instance-prefixed key while
// the reads asked by the bare name, so a child's initialized union carried
// no tag: the valid member still read -7 (a missing tag skips the check), but
// the read of `w.Valid` against tag Invalid raised nothing.
TEST(TaggedUnionEval, ChildInstanceDeclarationInitializerTagChecksMemberRead) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid -7;\n"
      "  u_t w = tagged Invalid;\n"
      "  int x;\n"
      "  int y;\n"
      "  initial begin\n"
      "    x = u.Valid;\n"
      "    y = w.Valid;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("m.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 9, "11.9"));
}

// §11.9 with §23.9: the procedural `u = tagged B 9` inside the child replaces
// the tag the declaration initializer set on the same variable, so the read
// of `u.B` is consistent and `u.A` is the mismatch. Both forms write one
// union, so a fix keying one of them differently from the other leaves the
// declaration's tag A standing: `u.B` would then be reported and `u.A` not.
TEST(TaggedUnionEval, ChildInstanceProceduralTagReplacesDeclarationTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u = tagged A 5;\n"
      "  int x;\n"
      "  int y;\n"
      "  initial begin\n"
      "    u = tagged B 9;\n"
      "    x = u.B;\n"
      "    y = u.A;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("m.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member", 9, "11.9"));
}

// §21.2.1.6 with §11.9 and §23.9: %p prints a tagged union as its valid
// member, "tag:value", the tag being the one the child's declaration
// initializer set. Read by the bare name, the tag was missing and the union
// fell to the untagged form, which prints the first declared member.
TEST(TaggedUnionEval, ChildInstanceDeclarationInitializerPrintsTagAndValue) {
  SimFixture f;
  auto out = RunCapture(
      "module M;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid -7;\n"
      "  initial $display(\"%p\", u);\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:-7}\n");
}

// §13.5.1 with §7.3.2 and §11.9: the actual is copied into the subroutine's
// own variable, and a tagged union's value is its tag beside the member
// value (§7.3.2, printed page 151), so the copy carries the tag and a member
// access of the formal inside the body is checked against it. The formal
// took the bits alone: `a.Valid` of a formal bound from a union holding
// `tagged Invalid` was read against no tag and raised nothing. The same
// function is called with the Valid union first so that a tag left standing
// from an earlier call is told apart from the actual's own.
TEST(TaggedUnionEval, ByValueFormalCarriesTheActualsTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid -7;\n"
      "  u_t w = tagged Invalid;\n"
      "  int x;\n"
      "  int y;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = f(u);\n"
      "    y = f(w);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "tagged union 'a' which currently has tag 'Valid'",
                             8, "11.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 8, "11.9"));
}

// §13.5 (printed page 348): the return passes an output formal's value to
// the caller's variable, tag and all, so `o = tagged Valid 4` inside the task
// leaves the actual holding Valid: `u.Valid` is then consistent and
// `u.Other`, the tag the actual held before the call, is the mismatch. Before
// this the actual kept tag Other, so line 11 was reported and line 12 read
// 1 unreported.
TEST(TaggedUnionEval, OutputFormalCarriesItsTagBackToTheActual) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  u_t u = tagged Other 1;\n"
      "  int x;\n"
      "  int y;\n"
      "  task retag(output u_t o);\n"
      "    o = tagged Valid 4;\n"
      "  endtask\n"
      "  initial begin\n"
      "    retag(u);\n"
      "    x = u.Valid;\n"
      "    y = u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 4u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 11, "11.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "tagged union 'u' which currently has tag 'Valid'",
                            12, "11.9"));
}

// §21.2.1.6 with §13.5.1: %p of the formal prints the tag the actual was
// copied in with, "tag:value". With no tag on the formal the union fell to
// the untagged form, which prints the first declared member.
TEST(TaggedUnionEval, ByValueFormalPrintsTheActualsTagAndValue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  u_t u = tagged Valid -7;\n"
      "  function void show(u_t a);\n"
      "    $display(\"%p\", a);\n"
      "  endfunction\n"
      "  initial show(u);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:-7}\n");
}

// §11.9 (printed page 303): a tagged union expression names a member and
// gives the value that tag, and (printed 304) its type is known from its
// context -- here the formal it is the actual of. §13.5.1 (printed 348)
// copies the actual's value into the subroutine's own variable, and §7.3.2
// (printed 151) has that value carry the tag beside the member's bits. The
// binding resolved the layout and the tag from an identifier actual's
// storage alone, which a tagged expression has none of, so `f(tagged Valid
// -7)` bound neither to the formal and `a.Valid` inside the body was read
// through no member.
TEST(TaggedUnionEval, TaggedExprActualBindsTheFormalsLayoutAndTag) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial x = f(tagged Valid -7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFF9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 5, "11.9"));
}

// §11.9 (printed page 304): a member access inconsistent with the current
// tag is a run-time error, and the formal's tag is the member the actual
// names. With no tag bound from a tagged-expression actual, `a.Valid` of a
// formal passed `tagged Invalid` raised nothing.
TEST(TaggedUnionEval, TaggedExprActualOfVoidMemberIsCheckedInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } u_t;\n"
      "  int y;\n"
      "  function int f(u_t a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial y = f(tagged Invalid);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 5, "11.9"));
}

// §7.2 with §11.9: a member of the formal is the window the union's layout
// gives it, so `a.Small` of an 8-bit member is 8 bits wide and the
// self-determined concatenation `{a.Small, a.Small}` (§11.4.12) is 16 wide,
// 16'hABAB; read through no layout the member resolved to nothing, and read
// as the union's whole 32 bits the concatenation would be 64 wide and the
// int take its low 32, 32'h000000AB. `a.Other` reads the wider member's
// value through the same layout.
TEST(TaggedUnionEval, TaggedExprActualNarrowMemberReadsItsOwnWindow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { void Invalid; bit [7:0] Small; int Other; }"
      " u_t;\n"
      "  int z;\n"
      "  int w;\n"
      "  function int g(u_t a);\n"
      "    return {a.Small, a.Small};\n"
      "  endfunction\n"
      "  function int h(u_t a);\n"
      "    return a.Other;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    z = g(tagged Small 8'hAB);\n"
      "    w = h(tagged Other 32'h12345678);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->value.ToUint64(), 0xABABu);
  auto* w = f.ctx.FindVariable("w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.ToUint64(), 0x12345678u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 6, "11.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 9, "11.9"));
}

// §11.9 (printed page 304): the braces of a tagged union expression are a
// §10.9.2 structure assignment pattern, and §10.9.2 (printed 263) evaluates
// each member expression in the context of an assignment to the member it
// initializes, in declaration order. As an actual the pattern was evaluated
// with no type to place it by, so `'{8'd1, 8'd2}` was concatenated at its
// elements' self-determined widths, 16'h0102, and zero-extended into the
// union: `u.Add.a` read 0 and `u.Add.b` read 258, the body 258 where §10.9.2
// gives 12.
TEST(TaggedUnionEval, TaggedPatternActualIsPlacedByMemberPosition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  typedef union tagged { void None; pair_t Add; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t u);\n"
      "    return u.Add.a * 10 + u.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{8'd1, 8'd2});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 6, "11.9"));
}

// §10.9.2 (printed page 263): a structure assignment pattern may name its
// members, in any order. Concatenated in written order, `'{b: 2, a: 1}` put
// 2 where `a` lies and 1 where `b` lies, and the body read 21; placed by
// member it reads 12.
TEST(TaggedUnionEval, TaggedPatternActualIsPlacedByMemberName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  typedef union tagged { void None; pair_t Add; } u_t;\n"
      "  int x;\n"
      "  function int f(u_t u);\n"
      "    return u.Add.a * 10 + u.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{b: 2, a: 1});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
}

// §13.3 (printed page 337) declares a formal with any data_type, a tagged
// union written inline among them, and §11.9 (printed 304) has the tagged
// expression's type known from the formal. An inline type names no
// registered layout, so the formal was bound as a plain vector: `a.Valid`
// was read through no member and answered 1 bit, not 5. The layout is built
// from the formal's own type and registered under the formal's name.
TEST(TaggedUnionEval, TaggedExprActualBindsAnInlineUnionFormalsLayout) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  function int f(union tagged { void Invalid; int Valid; } a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial x = f(tagged Valid 5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 4, "11.9"));
}

// §11.9 (printed page 304): a member access inconsistent with the current
// tag is a run-time error, and the formal's tag is the member the actual
// names, whether the formal's union is named by a typedef or written inline.
// With no layout bound, `a.Valid` of an inline-typed formal passed `tagged
// Invalid` raised nothing.
TEST(TaggedUnionEval, TaggedExprActualOfInlineUnionFormalIsCheckedInTheBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int y;\n"
      "  function int f(union tagged { void Invalid; int Valid; } a);\n"
      "    return a.Valid;\n"
      "  endfunction\n"
      "  initial y = f(tagged Invalid);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "tagged union 'a' which currently has tag 'Invalid'", 4, "11.9"));
}

// §13.3 (printed page 337) declares a formal with any data_type, and §7.2.1
// (printed 147) lays an inline union out member by member, `pair_t Add`
// naming a typedef of a structure of its own. The elaborator resolved a
// member's typedef for the typedef table and a declaration alone, so the
// formal's own type carried none: the union was sized as if Add were a
// scalar, its layout gave Add no members to place `'{3, 4}` by or to read
// `a.Add.a` through, and the body answered 0 where §10.9.2 (printed 263)
// places 3 into a and 4 into b, 34.
TEST(TaggedUnionEval,
     TaggedPatternActualOfInlineUnionFormalReadsANestedTypedefMember) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a, b; } pair_t;\n"
      "  int x;\n"
      "  function int f(union tagged { void None; pair_t Add; } a);\n"
      "    return a.Add.a * 10 + a.Add.b;\n"
      "  endfunction\n"
      "  initial x = f(tagged Add '{3, 4});\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 34u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 5, "11.9"));
}

}  // namespace
