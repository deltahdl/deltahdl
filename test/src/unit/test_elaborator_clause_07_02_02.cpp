// §7.2.2: Assigning to structures


#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §7.2.2: Packed struct members shall not have individual default values.
TEST(Elaboration, PackedStructMemberDefault_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct packed { bit [3:0] lo = 5; bit [3:0] hi; } s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, UnpackedStructMemberDefault_Allowed) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  struct { int a = 1; int b = 2; } s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
