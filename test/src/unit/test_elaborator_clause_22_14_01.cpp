#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The variable of module `mod` named `name`, or nullptr when there is none.
const RtlirVariable* FindVar(RtlirDesign* design, std::string_view mod,
                             std::string_view name) {
  auto it = design->all_modules.find(mod);
  if (it == design->all_modules.end()) return nullptr;
  for (const auto& var : it->second->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

// §22.14.1's second example carried all the way to an elaborated design. Under
// a 1364-2001 region `logic` is an ordinary identifier, so it names the
// module's 64-bit variable — and the elaborated module really does hold a
// variable under that name and width, which is what shows the word survived as
// a declaration rather than merely getting past the parser.
TEST(KeywordVersionExampleElab, VerilogRegionElaboratesLogicAsAVariable) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n"
      "module m2 (input wire clk, output wire q);\n"
      "  reg [63:0] logic;\n"
      "endmodule\n"
      "`end_keywords\n",
      f, "m2");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* var = FindVar(design, "m2", "logic");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->width, 64u);
}

// The example's variable is a packed 64-bit `reg`, but the region frees the
// identifier rather than one declaration form. Carried through elaboration,
// the freed word names a variable of each type a module of that era could
// declare, and each arrives with the storage its own type implies — a
// different path through the elaborator than the packed vector above.
TEST(KeywordVersionExampleElab,
     VerilogRegionElaboratesLogicAsEveryVariableType) {
  struct Case {
    const char* decl;
    uint32_t width;
    bool is_real;
  };
  const Case kCases[] = {
      {"reg logic;", 1, false},
      {"integer logic;", 32, false},
      {"time logic;", 64, false},
      {"real logic;", 64, true},
  };
  for (const auto& c : kCases) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        std::string("`begin_keywords \"1364-2001\"\nmodule t;\n  ") + c.decl +
            "\nendmodule\n`end_keywords\n",
        f, "t");
    ASSERT_NE(design, nullptr) << c.decl;
    EXPECT_FALSE(f.has_errors) << c.decl;

    const auto* var = FindVar(design, "t", "logic");
    ASSERT_NE(var, nullptr) << c.decl;
    EXPECT_EQ(var->width, c.width) << c.decl;
    EXPECT_EQ(var->is_real, c.is_real) << c.decl;
  }
}

// §22.14.1's fourth example: the region names this standard, whose reserved
// word list makes `interface`/`endinterface` keywords, so the declaration
// elaborates as an interface — a §3.2 design element of a kind other than a
// module, and a distinct input form for the region. The instantiating module
// sits outside the pair, under the default list, and still binds to it.
TEST(KeywordVersionExampleElab, SystemVerilogRegionElaboratesTheInterface) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "interface if1 (input wire clk);\n"
      "  wire [7:0] data;\n"
      "endinterface\n"
      "`end_keywords\n"
      "module top;\n"
      "  wire c;\n"
      "  if1 u (.clk(c));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  auto it = design->all_modules.find("if1");
  ASSERT_NE(it, design->all_modules.end());
  EXPECT_TRUE(it->second->is_interface);
  ASSERT_EQ(it->second->nets.size(), 1u);
  EXPECT_EQ(it->second->nets[0].name, "data");
}

// §22.14.1's first example: with no directive governing it, the module is
// elaborated under the implementation's default reserved word list. This
// implementation's default is 1800-2023, and the positive witness for that is
// that `logic` works here as the type keyword the newer lists reserve — the
// opposite role it plays inside the 1364-2001 region above, from the same
// spelling of the word.
TEST(KeywordVersionExampleElab, ModuleWithNoDirectiveUsesTheDefaultList) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module m1;\n"
      "  logic [63:0] v;\n"
      "endmodule\n",
      f, "m1");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* var = FindVar(design, "m1", "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->width, 64u);
  EXPECT_EQ(FindVar(design, "m1", "logic"), nullptr);
}

}  // namespace
