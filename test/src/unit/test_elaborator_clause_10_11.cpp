#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// §10.11 Net alias — elaboration
// =============================================================================

TEST(ElabClause1011, NetAliasNotSilentlyIgnored) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b;\n"
                              "  alias a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->aliases.size(), 1u);
  ASSERT_EQ(mod->aliases[0].nets.size(), 2u);
}

TEST(ElabClause1011, NetAliasThreeNets) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b, c;\n"
                              "  alias a = b = c;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->aliases.size(), 1u);
  ASSERT_EQ(mod->aliases[0].nets.size(), 3u);
}

// =============================================================================
// §10.11 Net alias — validation (not yet implemented)
// =============================================================================

TEST(ElabClause1011, Validate_NetAlias_TypeCompatibility) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire [7:0] a;\n"
               "  wire [15:0] b;\n"
               "  alias a = b;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_SameTypeOk) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire [7:0] a, b;\n"
               "  alias a = b;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_NoVariables) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  logic a;\n"
               "  wire b;\n"
               "  alias a = b;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_NoSelfAlias) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire a;\n"
               "  alias a = a;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1011, Validate_NetAlias_ImplicitNetCreation) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a;\n"
                              "  alias a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}
