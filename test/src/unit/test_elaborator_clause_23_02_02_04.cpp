
#include "fixture_elaborator.h"

namespace {

TEST(DefaultPortValueElaboration, InputPortWithDefaultElaborates) {
  EXPECT_TRUE(ElabOk("module m(input logic a = 1'b0); endmodule"));
}

TEST(DefaultPortValueElaboration, OutputPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc("module m(output logic q = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DefaultPortValueElaboration, InterconnectPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc("module m(input interconnect x = 1'b0); endmodule", f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DefaultPortValueElaboration, NonSingularPortWithDefaultIsError) {
  ElabFixture f;
  ElaborateSrc("module m(input logic x [3:0] = '{0, 0, 0, 0}); endmodule", f,
               "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(DefaultPortValueElaboration, OmittedInputUsesDefaultNamedConn) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
      "  assign a = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(.a(x));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
