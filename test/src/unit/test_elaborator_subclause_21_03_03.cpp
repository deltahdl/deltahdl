#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §21.3.3: the first argument to $swrite (and the output variable of $sformat)
// shall be a variable of an integral, unpacked-array-of-byte, or string type.
// A string-typed destination is the canonical accepting form and elaborates.
TEST(StringFormatTaskElaboration, SwriteStringOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial $swrite(s, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3: an integral destination is an admitted form of the output-variable
// rule. Built from a real packed-vector declaration so elaboration resolves the
// reference and accepts the call.
TEST(StringFormatTaskElaboration, SwriteIntegralOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] v;\n"
      "  initial $swrite(v, \"%h\", 8'hab);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3: an unpacked array of byte is an admitted output-variable form. Built
// from a real unpacked-array declaration so elaboration resolves the reference
// and accepts the call rather than rejecting it as a disallowed type.
TEST(StringFormatTaskElaboration, SwriteUnpackedByteArrayOutputVarAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b [0:3];\n"
      "  initial $swrite(b, \"ABCD\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §21.3.3 negative form: the output variable "shall be a variable of integral,
// unpacked array of byte, or string data types" -- a real destination has no
// character representation and is the closest illegal form. $swrite into a real
// variable shall be rejected.
TEST(StringFormatTaskElaboration, SwriteRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $swrite(r, \"x=%0d\", 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §21.3.3 negative form for $sformat: its output variable is subject to the
// same rule, so a real destination is likewise rejected.
TEST(StringFormatTaskElaboration, SformatRealOutputVarRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  initial $sformat(r, \"v=%0d\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §21.3.3: $sformatf takes no output variable -- its first argument is the
// format string and its result is the function return value. A real target for
// the RESULT (assigned from the function value) is a different rule and must
// not trip the output-variable check; the format-only call elaborates cleanly.
TEST(StringFormatTaskElaboration, SformatfHasNoOutputVarCheck) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = $sformatf(\"val=%0d\", 42);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
