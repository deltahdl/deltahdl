#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh6bFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh6bFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// --------------------------------------------------------------------------
// §6.11.1: type(expression) used in `var type(expr) name;` declarations.
// The type operator resolves to the same type, width, and signedness as
// the referenced expression.
// --------------------------------------------------------------------------

// 1. type() with int: resolves to 32-bit signed.
TEST(SimCh6b, TypeOpInt) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    b = 99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 99u);
  EXPECT_TRUE(var->is_signed);
}

// 2. type() with logic: resolves to 1-bit unsigned.
TEST(SimCh6b, TypeOpLogic) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  EXPECT_FALSE(var->is_signed);
}

// 3. type() with byte: resolves to 8-bit signed.
TEST(SimCh6b, TypeOpByte) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 8'hAB;\n"
      "    b = 8'hCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
  EXPECT_TRUE(var->is_signed);
}

// 4. type() with shortint: resolves to 16-bit signed.
TEST(SimCh6b, TypeOpShortint) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 16'h1234;\n"
      "    b = 16'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
  EXPECT_TRUE(var->is_signed);
}

// 5. type() with longint: resolves to 64-bit signed.
TEST(SimCh6b, TypeOpLongint) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 64'hDEAD_BEEF_CAFE_BABE;\n"
      "    b = 64'h0123_4567_89AB_CDEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x0123456789ABCDEFu);
  EXPECT_TRUE(var->is_signed);
}

// 6. type() with integer: resolves to 32-bit signed (4-state).
TEST(SimCh6b, TypeOpInteger) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  integer a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 32'hDEAD;\n"
      "    b = 32'hBEEF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
  EXPECT_TRUE(var->is_signed);
}

// 7. type() with real: resolves to 64-bit real variable.
TEST(SimCh6b, TypeOpReal) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  real a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 3.14;\n"
      "    b = 2.71;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
}

// 8. type() preserves signed flag from int source.
TEST(SimCh6b, TypeOpPreservesSignedInt) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = -1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);
  // -1 in 32-bit = 0xFFFFFFFF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

// 9. type() preserves unsigned flag from scalar logic source.
TEST(SimCh6b, TypeOpPreservesUnsignedLogic) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  var type(a) result;\n"
      "  initial result = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->is_signed);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// 10. type() with shortint source: 16-bit width preserved via type operator.
TEST(SimCh6b, TypeOpShortintWidth16) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 16'hCAFE;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// 11. type() with integer source: 32-bit width preserved via type operator.
TEST(SimCh6b, TypeOpIntegerWidth32) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  integer a;\n"
      "  var type(a) result;\n"
      "  initial result = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// 12. type() preserves width across assignment — value truncated to type width.
TEST(SimCh6b, TypeOpWidthTruncation) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 32'hFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  // 0xFFFF truncated to 8 bits = 0xFF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// 13. type() referencing int, both variables assigned different values.
TEST(SimCh6b, TypeOpIntDifferentValues) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 1000;\n"
      "    b = 2000;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *va = f.ctx.FindVariable("a");
  auto *vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.width, vb->value.width);
  EXPECT_EQ(va->value.ToUint64(), 1000u);
  EXPECT_EQ(vb->value.ToUint64(), 2000u);
}

// 14. type() with signed shortint — verify sign extension on assignment.
TEST(SimCh6b, TypeOpShortintSignExtension) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    result = a;\n"
      "    wide = result;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_TRUE(var->is_signed);
  // -1 in 16 bits = 0xFFFF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

// 15. type() with packed struct member type via intermediate int.
TEST(SimCh6b, TypeOpStructMemberWidth) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] field_a;\n"
      "    logic [7:0] field_b;\n"
      "  } my_struct;\n"
      "  my_struct s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = 16'hCAFE;\n"
      "    result = s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// 16. type() used with parameter default value type (parameter type T = int).
TEST(SimCh6b, TypeOpParameterTypeDefault) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "  var type(x) result;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    result = 77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// 17. type() with enum-typed variable preserves 32-bit enum width.
TEST(SimCh6b, TypeOpEnumType) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  var type(c) result;\n"
      "  initial begin\n"
      "    c = GREEN;\n"
      "    result = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // enum default base type is int (32-bit).
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// 18. type() referencing byte preserves 8-bit width in computation.
TEST(SimCh6b, TypeOpByteComputation) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    a = 100;\n"
      "    result = a + 50;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  // 100 + 50 = 150, which fits in 8 bits.
  EXPECT_EQ(var->value.ToUint64(), 150u);
}

// 19. type() with int preserves width when result overflows.
TEST(SimCh6b, TypeOpIntOverflow) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'hFFFF_FFFF_1234_5678;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  // Truncated to 32 bits: 0x12345678.
  EXPECT_EQ(var->value.ToUint64(), 0x12345678u);
}

// 20. type() on int, verify both source and destination have same width.
TEST(SimCh6b, TypeOpMatchingWidths) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *va = f.ctx.FindVariable("a");
  auto *vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.width, vb->value.width);
  EXPECT_EQ(va->is_signed, vb->is_signed);
}

// 21. type() with byte, verify full 8-bit range.
TEST(SimCh6b, TypeOpByteFullRange) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// 22. type() with longint source: 64-bit value preserved.
TEST(SimCh6b, TypeOpLongintFullValue) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'hCAFEBABE_DEADBEEF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEDEADBEEFu);
}

// 23. type() with byte, verify unsigned flag is not set (byte is signed).
TEST(SimCh6b, TypeOpByteIsSigned) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial result = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->is_signed);
  EXPECT_EQ(var->value.width, 8u);
}

// 24. type() with longint, assign max value.
TEST(SimCh6b, TypeOpLongintMaxValue) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  longint a;\n"
      "  var type(a) result;\n"
      "  initial result = 64'h7FFF_FFFF_FFFF_FFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_EQ(var->value.ToUint64(), 0x7FFFFFFFFFFFFFFFu);
  EXPECT_TRUE(var->is_signed);
}

// 25. type() with shortint, assign zero.
TEST(SimCh6b, TypeOpShortintZero) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
  EXPECT_TRUE(var->is_signed);
}

// 26. type() with byte preserves signedness in arithmetic context.
TEST(SimCh6b, TypeOpByteArithmeticSigned) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    a = 100;\n"
      "    result = a + 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_TRUE(var->is_signed);
  // 100 + 55 = 155.
  EXPECT_EQ(var->value.ToUint64(), 155u);
}

// 27. type() with int, chained: type(a) b, type(b) c.
TEST(SimCh6b, TypeOpChainedTypeRef) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) b;\n"
      "  var type(b) c;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    c = 30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *vc = f.ctx.FindVariable("c");
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(vc->value.width, 32u);
  EXPECT_EQ(vc->value.ToUint64(), 30u);
  EXPECT_TRUE(vc->is_signed);
}

// 28. type() with int, value preserved after multiple assignments.
TEST(SimCh6b, TypeOpMultipleAssignments) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  int a;\n"
      "  var type(a) result;\n"
      "  initial begin\n"
      "    result = 1;\n"
      "    result = 2;\n"
      "    result = 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// 29. type() with shortint, assign max unsigned 16-bit value.
TEST(SimCh6b, TypeOpShortintMaxUnsigned) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  shortint a;\n"
      "  var type(a) result;\n"
      "  initial result = 16'hFFFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
  EXPECT_TRUE(var->is_signed);
}

// 30. type() from byte, assigned via expression from wider variable.
TEST(SimCh6b, TypeOpByteFromWiderAssignment) {
  SimCh6bFixture f;
  auto *design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  var type(a) result;\n"
      "  int wide;\n"
      "  initial begin\n"
      "    wide = 32'h12345678;\n"
      "    result = wide;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  // 0x12345678 truncated to 8 bits = 0x78.
  EXPECT_EQ(var->value.ToUint64(), 0x78u);
  EXPECT_TRUE(var->is_signed);
}
