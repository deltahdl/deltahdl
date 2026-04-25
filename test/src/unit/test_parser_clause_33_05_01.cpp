#include <gtest/gtest.h>

#include "fixture_parser.h"

namespace {

// §33.5.1: every cell description from the input source ends up in the
// library, even when the cell is never referenced from another module.
// Here `top` instantiates `used`, while `unused` has no instantiator.
// Both must still appear in the parsed compilation unit and both must
// carry a non-empty library identifier — the §33.3.1 "work" fallback
// when no library map has explicitly tagged them.
TEST(SinglePassPrecompile, UnreferencedModuleStillInLibrary) {
  auto pr = Parse(
      "module unused;\n"
      "endmodule\n"
      "module used;\n"
      "endmodule\n"
      "module top;\n"
      "  used u();\n"
      "endmodule\n");
  ASSERT_FALSE(pr.has_errors);
  ASSERT_NE(pr.cu, nullptr);
  EXPECT_EQ(pr.cu->modules.size(), 3u);

  auto find_mod = [&](std::string_view name) -> ModuleDecl* {
    for (auto* m : pr.cu->modules) {
      if (m->name == name) return m;
    }
    return nullptr;
  };
  auto* unused = find_mod("unused");
  auto* used = find_mod("used");
  auto* top = find_mod("top");
  ASSERT_NE(unused, nullptr);
  ASSERT_NE(used, nullptr);
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(unused->library, "work");
  EXPECT_EQ(used->library, "work");
  EXPECT_EQ(top->library, "work");
}

// Every cell-kind design element (§33.2.1: modules, interfaces,
// programs, primitives, packages, configurations) parsed from the
// command-line input is mapped into the library by default.  The
// fallback library identifier is "work" per §33.3.1.
TEST(SinglePassPrecompile, AllCellKindsDefaultToWork) {
  auto pr = Parse(
      "module m;\n"
      "endmodule\n"
      "interface i;\n"
      "endinterface\n"
      "program p;\n"
      "endprogram\n"
      "primitive u(output o, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "package pk;\n"
      "endpackage\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_FALSE(pr.has_errors);
  ASSERT_EQ(pr.cu->modules.size(), 1u);
  ASSERT_EQ(pr.cu->interfaces.size(), 1u);
  ASSERT_EQ(pr.cu->programs.size(), 1u);
  ASSERT_EQ(pr.cu->udps.size(), 1u);
  ASSERT_EQ(pr.cu->packages.size(), 1u);
  ASSERT_EQ(pr.cu->configs.size(), 1u);

  EXPECT_EQ(pr.cu->modules[0]->library, "work");
  EXPECT_EQ(pr.cu->interfaces[0]->library, "work");
  EXPECT_EQ(pr.cu->programs[0]->library, "work");
  EXPECT_EQ(pr.cu->udps[0]->library, "work");
  EXPECT_EQ(pr.cu->packages[0]->library, "work");
  EXPECT_EQ(pr.cu->configs[0]->library, "work");
}

}  // namespace
