#include <string>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_logic4vec_string.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

static std::string ReadString(const Variable* var) {
  if (!var) return {};
  return Logic4VecToPackedString(var->value);
}

// §21.3.3 N17: $sformatf returns the formatted result as the function value.
TEST(StringFormatTaskTest, SformatfReturnsFormattedString) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$sformatf",
                           {MkStr(f.arena, "val=%d"), MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 48u);

  std::string formatted = Logic4VecToPackedString(result);
  EXPECT_EQ(formatted, "val=42");
}

// §21.3.3 N5, N6, N16: $swrite writes the formatted output into the variable
// named by its first argument, using string literal assignment to variable
// rules. The behaviour mirrors $fwrite but redirects to a variable instead of
// a file descriptor.
TEST(StringFormatTaskTest, SwriteWritesToOutputVariable) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("dst", 256);
  EvalExpr(MakeSysCall(f.arena, "$swrite",
                       {MkId(f.arena, "dst"), MkStr(f.arena, "x=%d y=%d"),
                        MakeInt(f.arena, 7), MakeInt(f.arena, 11)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "x=7 y=11");
}

// §21.3.3 N5 (cross-ref to §21.3.2): $swriteb / $swriteh / $swriteo derive
// their default radix from the task-name suffix when no format string is
// supplied, exactly as $fwriteb / $fwriteh / $fwriteo do.
TEST(StringFormatTaskTest, SwriteSuffixesUseRadix) {
  SimFixture f;
  struct Case {
    const char* task;
    uint64_t value;
    const char* expected;
  };
  const Case kCases[] = {
      {"$swriteh", 0xab, "ab"},
      {"$swriteo", 8, "10"},
      {"$swriteb", 5, "101"},
  };
  for (const auto& c : kCases) {
    std::string name = std::string("v_") + c.task;
    auto* dest = f.ctx.CreateVariable(name, 64);
    EvalExpr(MakeSysCall(f.arena, c.task,
                         {MkId(f.arena, name), MakeInt(f.arena, c.value)}),
             f.ctx, f.arena);
    EXPECT_EQ(ReadString(dest), c.expected) << "task=" << c.task;
  }
}

// §21.3.3 N9, N16: $sformat always treats its second argument as the format
// string and writes the formatted result into the first argument variable.
TEST(StringFormatTaskTest, SformatWritesUsingSecondArgAsFormat) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkStr(f.arena, "data is %d"),
                        MakeInt(f.arena, 123)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "data is 123");
}

// §21.3.3 N11: only the second argument of $sformat is treated as a format
// string; later string arguments are emitted verbatim through %s, never
// re-interpreted as another format template.
TEST(StringFormatTaskTest, SformatLaterStringArgIsNotFormatString) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkStr(f.arena, "tag=%s"),
                        MkStr(f.arena, "raw %d not interpreted")}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "tag=raw %d not interpreted");
}

// §21.3.3 N14: if not enough arguments are supplied for the format specifiers,
// or too many are supplied, the application shall issue a warning and
// continue execution.
TEST(StringFormatTaskTest, SformatArgCountMismatchEmitsWarning) {
  SimFixture f;
  f.ctx.CreateVariable("out", 256);

  uint32_t before = f.diag.WarningCount();
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkStr(f.arena, "a=%d b=%d"),
                        MakeInt(f.arena, 1)}),
           f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);

  before = f.diag.WarningCount();
  EvalExpr(MakeSysCall(
               f.arena, "$sformat",
               {MkId(f.arena, "out"), MkStr(f.arena, "only=%d"),
                MakeInt(f.arena, 1), MakeInt(f.arena, 2), MakeInt(f.arena, 3)}),
           f.ctx, f.arena);
  EXPECT_GT(f.diag.WarningCount(), before);
}

// §21.3.3 N10: the format argument of $sformatf can be an expression of
// integral, unpacked array of byte, or string data types whose content is
// interpreted as the formatting string (not only a string literal).
TEST(StringFormatTaskTest, SformatfFormatStringFromStringVariable) {
  SimFixture f;
  auto* fmt_var = f.ctx.CreateVariable("fmt", 56);
  fmt_var->value = StringToLogic4Vec(f.arena, "n=%0d");

  auto result =
      EvalExpr(MakeSysCall(f.arena, "$sformatf",
                           {MkId(f.arena, "fmt"), MakeInt(f.arena, 9)}),
               f.ctx, f.arena);
  std::string formatted = Logic4VecToPackedString(result);
  EXPECT_EQ(formatted, "n=9");
}

// §21.3.3 N5: the unsuffixed $swrite inherits the bare-expression rendering
// of $fwrite, which renders an unformatted integer in decimal. The b/h/o
// suffixes are exercised separately; this case observes the default arm.
TEST(StringFormatTaskTest, SwriteBareExpressionRendersDecimal) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 64);
  EvalExpr(MakeSysCall(f.arena, "$swrite",
                       {MkId(f.arena, "out"), MakeInt(f.arena, 255)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "255");
}

// §21.3.3 N10: the same prose that lets $sformatf accept a non-literal format
// argument applies to $sformat. A string-typed variable supplied as the second
// argument shall be decoded back into the formatting template.
TEST(StringFormatTaskTest, SformatFormatArgFromStringVariable) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  auto* fmt_var = f.ctx.CreateVariable("fmt", 56);
  fmt_var->value = StringToLogic4Vec(f.arena, "n=%0d");

  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkId(f.arena, "fmt"),
                        MakeInt(f.arena, 17)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "n=17");
}

// §21.3.3 N12: $sformat dispatches each specifier through the same format
// engine that $display uses (§21.2.1.1). %c, an ASCII-character specifier not
// otherwise observed by the %d/%s tests, confirms the linkage instead of
// merely the integer arm.
TEST(StringFormatTaskTest, SformatSupportsCharacterSpecifier) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkStr(f.arena, "ch=%c"),
                        MakeInt(f.arena, 'A')}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "ch=A");
}

// §21.3.3 N13: the remaining arguments are consumed in call order against the
// specifiers in the format string. A three-specifier call with mixed integer
// and string positions binds 1, "two", 3 left-to-right.
TEST(StringFormatTaskTest, SformatConsumesArgsInOrder) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"),
                        MkStr(f.arena, "a=%d, b=%s, c=%d"), MakeInt(f.arena, 1),
                        MkStr(f.arena, "two"), MakeInt(f.arena, 3)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "a=1, b=two, c=3");
}

// §21.3.3 N14 continuation: after issuing the count-mismatch warning, $sformat
// shall still continue execution. With more values supplied than the format
// string consumes, the extra value is dropped and the output variable receives
// the partially-formatted result rather than being left untouched.
TEST(StringFormatTaskTest, SformatContinuesAfterCountMismatchWarning) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("out", 256);
  EvalExpr(MakeSysCall(f.arena, "$sformat",
                       {MkId(f.arena, "out"), MkStr(f.arena, "v=%d"),
                        MakeInt(f.arena, 9), MakeInt(f.arena, 99)}),
           f.ctx, f.arena);
  EXPECT_EQ(ReadString(dest), "v=9");
}

// §21.3.3 N7: the resulting string is packed into the output variable with
// the leftmost character at the high byte position (left bound to right
// bound). With a four-character result "ABCD" in a 32-bit variable, byte 3
// (high) shall be 'A' and byte 0 (low) shall be 'D'.
TEST(StringFormatTaskTest, SwriteCharacterOrderingLeftToRight) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("o", 32);
  EvalExpr(MakeSysCall(f.arena, "$swrite",
                       {MkId(f.arena, "o"), MkStr(f.arena, "ABCD")}),
           f.ctx, f.arena);

  uint64_t bits = dest->value.words[0].aval;
  EXPECT_EQ(static_cast<char>((bits >> 24) & 0xFF), 'A');
  EXPECT_EQ(static_cast<char>((bits >> 16) & 0xFF), 'B');
  EXPECT_EQ(static_cast<char>((bits >> 8) & 0xFF), 'C');
  EXPECT_EQ(static_cast<char>(bits & 0xFF), 'D');
}

}  // namespace
