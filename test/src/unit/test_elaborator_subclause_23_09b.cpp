// Tests for the §23.9 scope rules as they reach a parameter declared inside a
// generate block. §23.9 lists "Generate blocks" among the elements that "define
// a new scope", and rules that an identifier "referenced directly (without a
// hierarchical path)" is declared "locally or within a module, interface,
// program, checker, task, function, named block, or generate block that is
// higher in the same branch of the name tree". Every case here states where a
// parameter is declared, where it is referenced from, and which of the two
// answers §23.9 gives.
//
// The cases over the rest of §23.9 -- one identifier declaring one item in a
// scope, and the upward search stopping at a module boundary -- are in
// test_elaborator_subclause_23_09a.cpp.

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The width of the one net of `mod` whose name is `name`, and 0 when no net or
// more than one carries it. The four cases below each declare a net whose
// packed range is written over a parameter, and read the width back to say
// which parameter the range folded against: a range that did not fold leaves
// the 1-bit base-type width §6.10 gives a scalar net.
uint32_t WidthOfNetNamed(const RtlirModule* mod, std::string_view name) {
  const RtlirNet* found = nullptr;
  for (const auto& net : mod->nets) {
    if (net.name != name) continue;
    if (found != nullptr) return 0;
    found = &net;
  }
  return found == nullptr ? 0 : found->width;
}

// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// and rules that an identifier "referenced directly (without a hierarchical
// path)" is declared "locally or within a module, interface, program, checker,
// task, function, named block, or generate block that is higher in the same
// branch of the name tree". Block 'a' is not higher in the module's own branch,
// so the W its localparam declares is not what the module-level range names,
// and `wire [W-1:0] w;` sizes to the 1 bit a scalar net gets.
//
// The test fails when the net is 4 bits wide. Elaborator::BuildParamScope in
// src/elaborator/elaborator_items_scope.cpp keys the ScopeMap every constant
// expression in the module folds against by RtlirParamDecl::name, which
// Elaborator::ElaborateParamDecl writes bare whatever scope declared the
// parameter, so block 'a''s W is entered under "W" and answers a range written
// anywhere in the module.
TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInAModuleLevelExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "  endgenerate\n"
      "  wire [W-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "w"), 1U)
      << "block 'a' localparam W should not size a module-level net";
}

// The same reading where the range stands in a sibling generate block. Blocks
// 'a' and 'c' are siblings, so neither is "higher in the same branch of the
// name tree" than the other and block 'a''s W is not what block 'c''s range
// names. Neither block is at module level, so the case cannot pass by
// Elaborator::ScopedName being the identity.
TEST(GenerateBlockScope,
     ParameterOfAGenerateBlockDoesNotFoldInASiblingBlockExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "    end\n"
      "    if (1) begin : c\n"
      "      wire [W-1:0] w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "c_w"), 1U)
      << "block 'a' localparam W should not size a sibling block's net";
}

// §11.2.1 makes a parameter a constant expression, and §23.9 rules that an
// identifier declared "locally" is what a direct reference names, so block
// 'a''s own W sizes a range written in block 'a'. The net is 4 bits wide.
//
// This is one of the two cases a fix must not lose: a scope that dropped every
// parameter carrying a generate block prefix would stop a block's parameter
// folding inside the block that declared it.
TEST(GenerateBlockScope, ParameterOfAGenerateBlockStillFoldsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam W = 4;\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "block 'a' localparam W should size a net in block 'a'";
}

// §23.9 rules that the search for a directly referenced identifier "shall
// continue upward until an item by that name is found or until a module,
// interface, program, or checker boundary is encountered", so a parameter of
// the module is found from inside every generate block in it. The net is 4 bits
// wide.
//
// This is the other case a fix must not lose, and it is the direction the
// defect does not run in: a module's parameter was always visible in a block,
// and a scope built for a block has to keep it so.
TEST(GenerateBlockScope, ParameterOfTheModuleStillFoldsInsideAGenerateBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  parameter W = 4;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      wire [W-1:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(WidthOfNetNamed(design->top_modules[0], "a_x"), 4U)
      << "the module's parameter W should size a net in block 'a'";
}

// The parameter of the one child instance of `mod`, which the four cases below
// read to see what a defparam wrote into it.
const RtlirParamDecl* OnlyChildParam(const RtlirModule* mod) {
  if (mod->children.size() != 1) return nullptr;
  const RtlirModule* child = mod->children[0].resolved;
  if (child == nullptr || child->params.size() != 1) return nullptr;
  return &child->params[0];
}

// §23.9 puts a generate block's declarations in a scope of their own, so the
// string parameter block 'a' declares is not what a defparam written among the
// module's own items names, and c.S keeps the default the child declared.
//
// A defparam is what reaches this reader. Elaborator::ApplyDefparams opens a
// ParamRangeRegistryGuard (src/elaborator/elaborator_defparam.cpp:343), and
// Elaborator::ResolveDefparamsAndGenerates (src/elaborator/elaborator.cpp:510)
// tests its break before processing a batch of pending generates, so defparams
// are applied once more after block 'a''s parameter is in RtlirModule::params.
// ConstEvalString sends a bare identifier straight to StringParamChars with no
// ScopeMap in between, which is why the scope Elaborator::BuildParamScope
// builds does not stand in the way here and why the registry has to carry the
// position itself.
//
// The test fails when c.S holds "abcd".
TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockIsNotReadByAModuleLevelDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "  endgenerate\n"
      "  defparam c.S = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_NE(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should not reach a module-level defparam";
}

// The direction the scope test must not lose, and the one that went red when
// the readers were given a test that refused every block-local parameter.
// §23.9 has an identifier "declared locally" name the local item, so a defparam
// written inside block 'a' does name block 'a''s P and c.S takes its
// characters.
//
// The instance stands in block 'a' beside the defparam and the localparam.
// §23.10.1 writes a defparam's target as a hierarchical path, and the path is
// what this case is not about: with the instance left at module level the
// defparam does not reach it from inside the block at all, so the case would
// report nothing about which P the right-hand side named.
TEST(GenerateBlockScope,
     StringParameterOfAGenerateBlockStillReadsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter string S = \"zz\")();\n"
      "endmodule\n"
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "      child c();\n"
      "      defparam c.S = P;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* s = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(std::string(s->resolved_string), "abcd")
      << "block 'a' localparam P should reach a defparam in block 'a'";
}

// The same rule at the other reader the registry answers. §6.16.1 gives
// `function int len()`, which ConstEvalBuiltinMethodFull folds through
// StringParamLength by reading RtlirParamDecl::resolved_string off the
// registered module, again with no ScopeMap in between. Block 'a''s P is four
// characters, so the test fails when c.N holds 4.
TEST(GenerateBlockScope,
     LengthOfAGenerateBlockStringParameterIsNotReadByAModuleLevelDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter N = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  child c();\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "    end\n"
      "  endgenerate\n"
      "  defparam c.N = P.len();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->resolved_value, 4)
      << "block 'a' localparam P should not give its length to a module-level "
         "defparam";
}

// StringParamLength's other direction, so it is held at both ends as
// StringParamChars is. Block 'a''s P is what a `len()` written in block 'a'
// names, and its four characters are what c.N takes.
TEST(GenerateBlockScope,
     LengthOfAGenerateBlockStringParameterStillReadsInsideThatBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter N = 9)();\n"
      "endmodule\n"
      "module top;\n"
      "  generate\n"
      "    if (1) begin : a\n"
      "      localparam string P = \"abcd\";\n"
      "      child c();\n"
      "      defparam c.N = P.len();\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const RtlirParamDecl* n = OnlyChildParam(design->top_modules[0]);
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->resolved_value, 4)
      << "block 'a' localparam P should give its length to a defparam in "
         "block 'a'";
}

}  // namespace
