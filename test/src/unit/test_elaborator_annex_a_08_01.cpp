// Tests for A.8.1 — Concatenations — Elaboration

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabA81Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA81Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

} // namespace

// =============================================================================
// A.8.1 Concatenations — Elaboration
// =============================================================================

// § concatenation elaborates in continuous assignment

TEST(ElabA81, ConcatenationInContAssign) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a;\n"
                              "  logic [3:0] x, y;\n"
                              "  assign a = {x, y};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_concatenation in parameter initialization

TEST(ElabA81, ConstantConcatenationInParam) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  parameter [15:0] P = {8'hAB, 8'hCD};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_multiple_concatenation in parameter

TEST(ElabA81, ConstantMultipleConcatInParam) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  parameter [31:0] P = {4{8'hFF}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § multiple_concatenation (replication) in continuous assignment

TEST(ElabA81, ReplicationInContAssign) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a;\n"
                              "  logic [1:0] x;\n"
                              "  assign a = {4{x}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § streaming_concatenation elaborates in procedural context

TEST(ElabA81, StreamingConcatLeftShiftElab) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a, b;\n"
                              "  initial a = {<< {b}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ElabA81, StreamingConcatRightShiftElab) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a, b;\n"
                              "  initial a = {>> {b}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § streaming_concatenation with slice_size elaborates

TEST(ElabA81, StreamingWithSliceSizeElab) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a, b;\n"
                              "  initial a = {<< byte {b}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § empty_unpacked_array_concatenation elaborates

TEST(ElabA81, EmptyUnpackedArrayConcatElab) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a;\n"
                              "  initial a = {};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § concatenation in initial block elaborates

TEST(ElabA81, ConcatInInitialBlock) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a;\n"
                              "  logic [3:0] x, y;\n"
                              "  initial a = {x, y};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § replication in initial block elaborates

TEST(ElabA81, ReplicateInInitialBlock) {
  ElabA81Fixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  logic [7:0] a;\n"
                              "  logic [1:0] x;\n"
                              "  initial a = {4{x}};\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
