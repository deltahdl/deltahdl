// §23.3: Module instances (hierarchy)

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"
#include <gtest/gtest.h>

using namespace delta;

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

namespace {

// --- Port binding tests ---
TEST(Elaboration, PortBinding_ResolvesChild) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a, output logic b);\n"
                              "  assign b = a;\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x, y;\n"
                              "  child u0(.a(x), .b(y));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "child");
  EXPECT_EQ(mod->children[0].port_bindings.size(), 2);
}

TEST(Elaboration, PortBinding_Direction) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a, output logic b);\n"
                              "  assign b = a;\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x, y;\n"
                              "  child u0(.a(x), .b(y));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  const auto &bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2);

  struct {
    const char *port_name;
    Direction direction;
  } const kExpected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kOutput},
  };
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(bindings[i].port_name, kExpected[i].port_name);
    EXPECT_EQ(bindings[i].direction, kExpected[i].direction);
  }
}

TEST(Elaboration, PortBinding_UnknownModule) {
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  logic x;\n"
                              "  nonexistent u0(.a(x));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  EXPECT_EQ(mod->children[0].resolved, nullptr);
}

TEST(Elaboration, PortBinding_PortMismatch) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child(input logic a);\n"
                              "endmodule\n"
                              "module top;\n"
                              "  logic x;\n"
                              "  child u0(.bogus(x));\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  // Port binding still created, but with warning.
  EXPECT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

} // namespace
