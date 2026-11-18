#include <gtest/gtest.h>

#include <array>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string InBlock(const std::string& construct, const std::string& name,
                    const std::string& body) {
  if (construct == "if") {
    return "  if (1) begin : " + name + "\n" + body + "  end\n";
  }
  if (construct == "else") {
    return "  if (0) begin : " + name + "_unused\n  end else begin : " + name +
           "\n" + body + "  end\n";
  }
  if (construct == "elseif") {
    return "  if (0) begin : " + name +
           "_unused\n  end else if (1) begin : " + name + "\n" + body +
           "  end\n";
  }
  if (construct == "case") {
    return "  case (1)\n    1: begin : " + name + "\n" + body +
           "    end\n  endcase\n";
  }
  return "  for (genvar i" + name + " = 0; i" + name + " < 1; i" + name +
         "++) begin : " + name + "\n" + body + "  end\n";
}

constexpr std::array<const char*, 5> kConstructs = {"if", "else", "elseif",
                                                    "case", "for"};

constexpr std::array<const char*, 4> kDeclarations = {
    "    int x = 2;\n", "    wire [31:0] x = 2;\n",
    "    localparam int x = 2;\n", "    typedef enum {A, x} e_t;\n"};

struct Read {
  const char* text;
  const char* body;
};

constexpr std::array<Read, 3> kReads = {
    {{"int v = x;", "    int v = x;\n"},
     {"assign w = x;", "    wire [31:0] w;\n    assign w = x;\n"},
     {"$display(x)", "    initial $display(x);\n"}}};

void ExpectUnresolvedAt(const std::string& src, const std::string& name,
                        const std::string& at) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier '" + name + "'",
                            LineHolding(src, at), "23.9"));
}

void ExpectNoError(const std::string& src) {
  SCOPED_TRACE(src);
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

void ExpectSiblingReadsUnresolved(const std::string& declaring,
                                  const std::string& reading) {
  for (const char* decl : kDeclarations) {
    for (const Read& read : kReads) {
      std::string src = "module m;\n";
      src += InBlock(declaring, "g1", decl);
      src += InBlock(reading, "g2", read.body);
      src += "endmodule\n";
      ExpectUnresolvedAt(src, "x", read.text);
    }
  }
}

TEST(GenerateBlockNameVisibility, ASiblingBlocksNameIsUnresolved) {
  for (const char* declaring : kConstructs) {
    for (const char* reading : kConstructs) {
      ExpectSiblingReadsUnresolved(declaring, reading);
    }
  }
}

TEST(GenerateBlockNameVisibility, ANestedBlocksNameIsUnresolvedAbove) {
  for (const char* outer : kConstructs) {
    for (const char* inner : kConstructs) {
      for (const Read& read : kReads) {
        ExpectUnresolvedAt(
            "module m;\n" +
                InBlock(outer, "g1",
                        InBlock(inner, "g3", "    int x = 2;\n") + read.body) +
                "endmodule\n",
            "x", read.text);
      }
    }
  }
}

TEST(GenerateBlockNameVisibility, ABlocksNameIsUnresolvedInTheDesignElement) {
  for (const std::string& element :
       {"module", "interface", "program", "checker"}) {
    for (const Read& read : kReads) {
      if (element == std::string("checker") &&
          read.text != std::string("int v = x;")) {
        continue;
      }
      std::string src = element;
      src += " m;\n";
      src += InBlock("if", "g1", "    int x = 2;\n");
      src += read.body;
      src += "end";
      src += element;
      src += "\nmodule top;\n  m u();\nendmodule\n";
      ExpectUnresolvedAt(src, "x", read.text);
    }
  }
}

TEST(GenerateBlockNameVisibility, ANameNoScopeDeclaresIsUnresolvedInABlock) {
  for (const char* construct : kConstructs) {
    for (const Read& read : kReads) {
      ExpectUnresolvedAt(
          "module m;\n" + InBlock(construct, "g1", read.body) + "endmodule\n",
          "x", read.text);
    }
  }
}

TEST(GenerateBlockNameVisibility, TheBlocksOwnNamesAreVisible) {
  for (const char* construct : kConstructs) {
    for (const char* decl : kDeclarations) {
      for (const Read& read : kReads) {
        ExpectNoError("module m;\n" +
                      InBlock(construct, "g1", std::string(decl) + read.body) +
                      "endmodule\n");
      }
    }
  }
}

TEST(GenerateBlockNameVisibility, AnEnclosingBlocksNamesAreVisible) {
  for (const char* outer : kConstructs) {
    for (const char* inner : kConstructs) {
      for (const Read& read : kReads) {
        ExpectNoError(
            "module m;\n" +
            InBlock(outer, "g1",
                    "    int x = 2;\n" +
                        InBlock(inner, "g3", InBlock("if", "g4", read.body))) +
            "endmodule\n");
      }
    }
  }
}

TEST(GenerateBlockNameVisibility, TheDesignElementsNamesAreVisibleInABlock) {
  for (const char* construct : kConstructs) {
    for (const Read& read : kReads) {
      ExpectNoError(
          "module m;\n  int x = 2;\n" +
          InBlock(construct, "g1", read.body + InBlock("if", "g3", read.body)) +
          "endmodule\n");
    }
  }
}

TEST(GenerateBlockNameVisibility, TheLoopGenvarIsVisibleInItsBody) {
  ExpectNoError(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g1\n"
      "    int v = i;\n"
      "    wire [31:0] w;\n"
      "    assign w = i;\n"
      "    initial $display(i);\n"
      "    if (1) begin : g3\n"
      "      int u = i;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
}

TEST(GenerateBlockNameVisibility, AModuleGenvarIsVisibleInTheLoopItSteps) {
  ExpectNoError(
      "module m;\n"
      "  genvar j;\n"
      "  for (j = 0; j < 2; j++) begin : g1\n"
      "    int v = j;\n"
      "    wire [31:0] w;\n"
      "    assign w = j;\n"
      "    initial $display(j);\n"
      "  end\n"
      "endmodule\n");
}

TEST(GenerateBlockNameVisibility, AnImportInTheBlockOrModuleIsVisible) {
  for (const std::string& import : {"import p::*;", "import p::x;"}) {
    for (const Read& read : kReads) {
      ExpectNoError("package p;\n  int x = 2;\nendpackage\nmodule m;\n" +
                    InBlock("if", "g1", "    " + import + "\n" + read.body) +
                    "endmodule\n");
      ExpectNoError("package p;\n  int x = 2;\nendpackage\nmodule m;\n  " +
                    import + "\n" + InBlock("if", "g1", read.body) +
                    "endmodule\n");
    }
  }
}

TEST(GenerateBlockNameVisibility, AnImportInASiblingBlockIsNotVisible) {
  for (const Read& read : kReads) {
    ExpectUnresolvedAt("package p;\n  int x = 2;\nendpackage\nmodule m;\n" +
                           InBlock("if", "g1", "    import p::*;\n") +
                           InBlock("if", "g2", read.body) + "endmodule\n",
                       "x", read.text);
  }
}

TEST(GenerateBlockNameVisibility, AHierarchicalNameReachesAnyBlock) {
  ExpectNoError(
      "module m;\n"
      "  if (1) begin : g1\n"
      "    int x = 2;\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    int v = g1.x;\n"
      "    wire [31:0] w;\n"
      "    assign w = g1.x;\n"
      "    initial $display(g1.x);\n"
      "  end\n"
      "  int u = g1.x;\n"
      "  initial $display(g1.x);\n"
      "endmodule\n");
}

TEST(GenerateBlockNameVisibility, APortConnectionDeclaresAnImplicitNet) {
  ExpectNoError(
      "module sub(input wire a);\n"
      "endmodule\n"
      "module m;\n"
      "  if (1) begin : g1\n"
      "    wire y = 1;\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    sub s(.a(y));\n"
      "    assign y = 1;\n"
      "  end\n"
      "endmodule\n");
}

}  // namespace
