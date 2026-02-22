// §24.3: The program construct

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Parse-level fixture
// =============================================================================
struct ProgramTestParse : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

// =============================================================================
// Elaboration fixture
// =============================================================================
struct ProgramElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSource(const std::string& src,
                                    ProgramElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

namespace {

TEST(ProgramElab, ElaborateProgramWithPorts) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_ports(input logic clk, input logic rst);\n"
      "endprogram\n",
      f, "prog_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(ProgramElab, ElaborateProgramWithInitialBlock) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_init;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n",
      f, "prog_init");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_FALSE(mod->processes.empty());
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

// =============================================================================
// §24.10 Program instantiation via elaboration
// =============================================================================
TEST(ProgramElab, ProgramInstantiatedFromModule) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program sub_prog(input logic a);\n"
      "endprogram\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_prog u0(.a(sig));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_prog");
}

}  // namespace
