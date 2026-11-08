#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

std::string RunSim(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  return testing::internal::GetCapturedStdout();
}

TEST(StringFormat, PrintsAsciiCodesAsCharacters) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'h4869;\n"
      "    $display(\"%s\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hi\n");
}

TEST(StringFormat, WriteTaskAndUppercaseSpelling) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v = 16'h4869;\n"
      "  initial $write(\"%S\", v);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hi");
}

TEST(StringFormat, DeclarationInitializerFromStringLiteral) {
  auto out = RunSim(
      "module t;\n"
      "  bit [39:0] v = \"Hello\";\n"
      "  initial $display(\"%s\", v);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Hello\n");
}

TEST(StringFormat, EachSpecifierConsumesItsOwnArgument) {
  auto out = RunSim(
      "module t;\n"
      "  byte c1, c2;\n"
      "  initial begin\n"
      "    c1 = \"A\";\n"
      "    c2 = \"B\";\n"
      "    $display(\"%s-%s\", c1, c2);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "A-B\n");
}

TEST(StringFormat, MissingArgumentContributesNothing) {
  auto out = RunSim(
      "module t;\n"
      "  initial $display(\"[%s]\");\n"
      "endmodule\n");
  EXPECT_EQ(out, "[]\n");
}

TEST(StringFormat, ValueRightJustifiedWhenWidthNotAByteMultiple) {
  auto out = RunSim(
      "module t;\n"
      "  bit [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'h341;\n"
      "    $display(\"%s\", v);\n"
      "  end\n"
      "endmodule\n");
  std::string expected;
  expected.push_back(static_cast<char>(0x03));
  expected += "A\n";
  EXPECT_EQ(out, expected);
}

TEST(StringFormat, LeadingZeroBytesAreNotPrinted) {
  auto out = RunSim(
      "module t;\n"
      "  bit [23:0] v;\n"
      "  initial begin\n"
      "    v = 24'h004142;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[AB]\n");
}

TEST(StringFormat, AllZeroValuePrintsNothing) {
  auto out = RunSim(
      "module t;\n"
      "  bit [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'h0000;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[]\n");
}

TEST(StringFormat, EmbeddedZeroByteIsPreserved) {
  auto out = RunSim(
      "module t;\n"
      "  bit [23:0] v;\n"
      "  initial begin\n"
      "    v = 24'h410042;\n"
      "    $display(\"[%s]\", v);\n"
      "  end\n"
      "endmodule\n");
  std::string expected = "[A";
  expected.push_back('\0');
  expected += "B]\n";
  EXPECT_EQ(out, expected);
}

TEST(StringFormat, StringTypedArgument) {
  auto out = RunSim(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"Verilog\";\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "Verilog\n");
}

TEST(StringFormat, StringTypedArgumentFromInitializer) {
  auto out = RunSim(
      "module t;\n"
      "  string s = \"Init\";\n"
      "  initial $display(\"%s\", s);\n"
      "endmodule\n");
  EXPECT_EQ(out, "Init\n");
}

TEST(StringFormat, ByteArrayAscendingRangePrintsLeftBoundFirst) {
  auto out = RunSim(
      "module t;\n"
      "  byte a [0:3];\n"
      "  initial begin\n"
      "    a[0] = \"A\";\n"
      "    a[1] = \"B\";\n"
      "    a[2] = \"C\";\n"
      "    a[3] = \"D\";\n"
      "    $display(\"%s\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "ABCD\n");
}

TEST(StringFormat, ByteArrayDescendingRangePrintsLeftBoundFirst) {
  auto out = RunSim(
      "module t;\n"
      "  byte a [3:0];\n"
      "  initial begin\n"
      "    a[0] = \"a\";\n"
      "    a[1] = \"b\";\n"
      "    a[2] = \"c\";\n"
      "    a[3] = \"d\";\n"
      "    $display(\"%s\", a);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "dcba\n");
}

TEST(StringFormat, ByteQueueAndDynamicArrayPrintTheirCharacters) {
  auto out = RunSim(
      "module t;\n"
      "  byte q[$] = {8'h68, 8'h69};\n"
      "  byte d[] = '{8'h6f, 8'h6b};\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%s %s\", q, d);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "hi ok\n");
}

TEST(StringFormat, FourStateIntegerOperand) {
  auto out = RunSim(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 'h4869;\n"
      "    $display(\"[%s]\", i);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[Hi]\n");
}

TEST(StringFormat, ConcatenationExpressionOperand) {
  auto out = RunSim(
      "module t;\n"
      "  byte c1, c2;\n"
      "  initial begin\n"
      "    c1 = \"H\";\n"
      "    c2 = \"i\";\n"
      "    $display(\"[%s]\", {c1, c2});\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "[Hi]\n");
}

TEST(StringFormat, SformatfPositionRendersSameCharacters) {
  auto out = RunSim(
      "module t;\n"
      "  logic [15:0] v;\n"
      "  string r;\n"
      "  initial begin\n"
      "    v = 16'h4F4B;\n"
      "    r = $sformatf(\"<%s>\", v);\n"
      "    $display(r);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(out, "<OK>\n");
}

TEST(StringFormat, NonByteUnpackedArrayIsRejected) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a [0:1];\n"
      "  initial begin\n"
      "    a[0] = 65;\n"
      "    a[1] = 66;\n"
      "    $display(\"[%s]\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  auto out = testing::internal::GetCapturedStdout();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a string format specifier applied to an unpacked "
                            "array",
                            6, "21.2.1.7"));
  EXPECT_EQ(out, "[]\n");
}

TEST(StringFormat, NonByteUnpackedArrayNames21_2_1_7) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int codes [0:1];\n"
      "  initial begin\n"
      "    codes[0] = 67;\n"
      "    codes[1] = 68;\n"
      "    $display(\"<%s>\", codes);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  testing::internal::CaptureStdout();
  LowerAndRun(design, f);
  testing::internal::GetCapturedStdout();
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a string format specifier applied to an unpacked array", 6, "21.2.1.7"));
}

}  // namespace
