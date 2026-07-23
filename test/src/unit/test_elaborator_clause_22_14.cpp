#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Returns the elaborated value of parameter `name` in module `mod`.
int64_t ParamValue(RtlirDesign* design, std::string_view mod,
                   std::string_view name) {
  auto it = design->all_modules.find(mod);
  EXPECT_NE(it, design->all_modules.end());
  if (it == design->all_modules.end()) return -1;
  for (const auto& param : it->second->params) {
    if (param.name == name) return param.resolved_value;
  }
  ADD_FAILURE() << "parameter not found: " << name;
  return -1;
}

// §22.14: the pair of directives only selects which identifiers are reserved
// words; it does not change the semantics of the language. The same design
// text elaborates to the same parameter values whether or not it sits inside a
// keyword region that names an older standard.
TEST(KeywordVersionElaboration, KeywordRegionDoesNotChangeElaboratedValues) {
  const std::string body =
      "module t;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = WIDTH * 4 + 1;\n"
      "  wire [DEPTH-1:0] w;\n"
      "endmodule\n";

  ElabFixture guarded;
  auto* with_region = ElaborateWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n" + body + "`end_keywords\n", guarded);
  ASSERT_NE(with_region, nullptr);
  EXPECT_FALSE(guarded.has_errors);

  ElabFixture plain;
  auto* without_region = ElaborateWithPreprocessor(body, plain);
  ASSERT_NE(without_region, nullptr);
  EXPECT_FALSE(plain.has_errors);

  EXPECT_EQ(ParamValue(with_region, "t", "WIDTH"),
            ParamValue(without_region, "t", "WIDTH"));
  EXPECT_EQ(ParamValue(with_region, "t", "DEPTH"), 33);
  EXPECT_EQ(ParamValue(with_region, "t", "DEPTH"),
            ParamValue(without_region, "t", "DEPTH"));
}

// §22.14: the reserved word list a `begin_keywords selects applies to all the
// source that follows it, so several design elements in one region are all
// elaborated under that list. `logic` names a net in both modules here.
TEST(KeywordVersionElaboration, OneRegionCoversSeveralDesignElements) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n"
      "module a;\n"
      "  wire logic;\n"
      "endmodule\n"
      "module b;\n"
      "  wire logic;\n"
      "  a inst ();\n"
      "endmodule\n"
      "`end_keywords\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  // Both design elements elaborated, and in each one the word the 1364-2001
  // list leaves unreserved really did come through as the net's name.
  for (std::string_view name : {"a", "b"}) {
    auto it = design->all_modules.find(name);
    ASSERT_NE(it, design->all_modules.end()) << name;
    ASSERT_EQ(it->second->nets.size(), 1u) << name;
    EXPECT_EQ(it->second->nets[0].name, "logic") << name;
  }
}

// §22.14 states its placement rule against the design elements of §3.2, and a
// region covers every kind of element that follows it, not just modules. A
// package and an interface written in real §3.2 syntax elaborate alongside the
// module inside one 1800-2005 region, and `until` — a word 1800-2005 has not
// yet reserved — really did come through as the package parameter's name.
TEST(KeywordVersionElaboration, RegionCoversNonModuleDesignElements) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "package pkg;\n"
      "  parameter until = 3;\n"
      "endpackage\n"
      "interface intf;\n"
      "  wire global;\n"
      "endinterface\n"
      "module t;\n"
      "  intf i ();\n"
      "endmodule\n"
      "`end_keywords\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ASSERT_EQ(design->packages.size(), 1u);
  EXPECT_EQ(design->packages[0]->name, "pkg");

  auto intf = design->all_modules.find("intf");
  ASSERT_NE(intf, design->all_modules.end());
  EXPECT_TRUE(intf->second->is_interface);
  ASSERT_EQ(intf->second->nets.size(), 1u);
  EXPECT_EQ(intf->second->nets[0].name, "global");
}

// §22.14: nested pairs are stacked. The inner region selects 1364-2001, where
// `logic` is an ordinary identifier; the enclosing region selects 1800-2012,
// where it is the type keyword. Both design elements elaborate, each under the
// list that was in effect where it appears.
TEST(KeywordVersionElaboration, NestedRegionsElaborateUnderOwnVersion) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "module inner;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module outer;\n"
      "  logic [3:0] v;\n"
      "  inner i ();\n"
      "endmodule\n"
      "`end_keywords\n",
      f, "outer");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto it = design->all_modules.find("inner");
  ASSERT_NE(it, design->all_modules.end());
  ASSERT_EQ(it->second->nets.size(), 1u);
  EXPECT_EQ(it->second->nets[0].name, "logic");
}

}  // namespace
