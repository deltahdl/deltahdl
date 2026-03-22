#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayRealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[real];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayShortrealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[shortreal];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration, RealtimeIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[realtime];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration, TypedefIntegralIndexAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  int aa[nibble_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeAssocArrayElaboration, EnumTypedefIndexAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  int aa[color_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(UserDefinedTypeAssocArrayElaboration, TypedefIndexNotStringOrWildcard) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit [7:0] octet_t;\n"
      "  int aa[octet_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto& vars = design->top_modules[0]->variables;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      EXPECT_FALSE(v.is_string_index);
      EXPECT_FALSE(v.is_wildcard_index);
    }
  }
}

}  // namespace
