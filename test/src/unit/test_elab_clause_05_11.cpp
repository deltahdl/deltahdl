#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// --- §5.11: Array literals ---

TEST(ElabCh511, ArrayInitPattern_FlatIllegal) {
  // §5.11: Nesting of braces shall follow the number of dimensions.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{0, 0, 1, 1};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabCh511, ArrayInitPattern_NestedOk) {
  // §5.11: Nested braces matching array dimensions are valid.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef struct { int a; int b; } ms_t;\n"
      "  ms_t ms[1:0] = '{'{0, 0}, '{1, 1}};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabCh511, ArrayInitPattern_SimpleArrayOk) {
  // §5.11 / §10.9.1: Expressions shall match element for element.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabCh511, ArrayInitPattern_SizeMismatch) {
  // §10.9.1: Expressions shall match element for element; 3 != 2.
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20, 30};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}
