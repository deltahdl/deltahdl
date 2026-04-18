#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Shared helper: parse + elaborate, returning the AST compilation unit so
// tests can observe names the elaborator writes onto generate ModuleItems.
struct NamedElab {
  ElabFixture f;
  CompilationUnit* cu = nullptr;
  RtlirDesign* design = nullptr;
};

NamedElab RunElaboration(const std::string& src, std::string_view top = "") {
  NamedElab r;
  auto fid = r.f.mgr.AddFile("<test>", src);
  Lexer lexer(r.f.mgr.FileContent(fid), fid, r.f.diag);
  Parser parser(lexer, r.f.arena, r.f.diag);
  r.cu = parser.Parse();
  if (!r.cu) return r;
  auto name = top.empty() ? r.cu->modules.back()->name : top;
  Elaborator elab(r.f.arena, r.f.diag, r.cu);
  r.design = elab.Elaborate(name);
  r.f.has_errors = r.f.diag.HasErrors();
  return r;
}

// §27.6: the first textual generate construct in a scope that lacks an
// explicit label must be assigned the name genblk1 during elaboration.
TEST(GenerateBlockNaming, FirstUnnamedConstructIsGenblk1) {
  auto r = RunElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(m->items[0]->name, "genblk1");
}

// §27.6: numbering in a scope increments by one per subsequent generate
// construct, so a second unnamed construct becomes genblk2.
TEST(GenerateBlockNaming, SecondUnnamedConstructIsGenblk2) {
  auto r = RunElaboration(
      "module top;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 2u);
  EXPECT_EQ(m->items[0]->name, "genblk1");
  EXPECT_EQ(m->items[1]->name, "genblk2");
}

// §27.6: an explicit generate block label suppresses genblk<n> assignment;
// the user-supplied name survives elaboration unchanged.
TEST(GenerateBlockNaming, ExplicitLabelIsRetained) {
  auto r = RunElaboration(
      "module top;\n"
      "  if (1) begin : my_block\n"
      "    logic a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 1u);
  EXPECT_EQ(m->items[0]->name, "my_block");
}

// §27.6 NOTE: the per-scope generate counter advances for every generate
// construct, including explicitly labeled ones.  So an unnamed construct
// following a labeled construct takes the next unused slot (here, slot 2 is
// still consumed by the labeled block so the unnamed block becomes genblk3
// if another labeled block precedes it - verify at least that numbering
// skips past the named construct).
TEST(GenerateBlockNaming, NumberingCountsNamedConstructs) {
  auto r = RunElaboration(
      "module top;\n"
      "  if (1) begin : first\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ASSERT_EQ(m->items.size(), 2u);
  EXPECT_EQ(m->items[0]->name, "first");
  // The second construct sits in slot 2, so its default name is genblk2 even
  // though the first slot was consumed by a labeled block.
  EXPECT_EQ(m->items[1]->name, "genblk2");
}

// §27.6: when the computed genblk<n> name would collide with an explicitly
// declared identifier in the same scope, leading zeros are prepended to the
// number until the name is unique (e.g. genblk02 when genblk2 is taken).
TEST(GenerateBlockNaming, CollisionResolvedByLeadingZero) {
  auto r = RunElaboration(
      "module top;\n"
      "  parameter genblk2 = 0;\n"
      "  if (1) begin\n"
      "    logic a;\n"
      "  end\n"
      "  if (1) begin\n"
      "    logic b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.design, nullptr);
  auto* m = r.cu->modules[0];
  ModuleItem* first = nullptr;
  ModuleItem* second = nullptr;
  int gen_seen = 0;
  for (auto* it : m->items) {
    if (it->kind != ModuleItemKind::kGenerateIf) continue;
    if (gen_seen++ == 0) {
      first = it;
    } else {
      second = it;
    }
  }
  ASSERT_NE(first, nullptr);
  ASSERT_NE(second, nullptr);
  EXPECT_EQ(first->name, "genblk1");
  // genblk2 collides with the parameter of the same name; one leading zero
  // is inserted to produce a unique default.
  EXPECT_EQ(second->name, "genblk02");
}

}  // namespace
