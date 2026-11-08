#include <gtest/gtest.h>

#include <string>

#include "fixture_vcd_dump_from_source.h"

using namespace delta;

namespace {

class DumpfileSysTask : public VcdDumpFromSourceTestBase {
 protected:
  std::string RunAndDumpName(const std::string& src) {
    RunSource(src);
    return f_.ctx.Vcd().GetDumpFileName();
  }
};

TEST_F(DumpfileSysTask, StringLiteralSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial $dumpfile(\"module1.dump\");\n"
                           "endmodule\n"),
            "module1.dump");
}

TEST_F(DumpfileSysTask, StringVariableSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  string fname;\n"
                           "  initial begin\n"
                           "    fname = \"wave.vcd\";\n"
                           "    $dumpfile(fname);\n"
                           "  end\n"
                           "endmodule\n"),
            "wave.vcd");
}

TEST_F(DumpfileSysTask, IntegralValueSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  reg [31:0] code;\n"
                           "  initial begin\n"
                           "    code = \"wave\";\n"
                           "    $dumpfile(code);\n"
                           "  end\n"
                           "endmodule\n"),
            "wave");
}

TEST_F(DumpfileSysTask, LaterCallReSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial begin\n"
                           "    $dumpfile(\"first.vcd\");\n"
                           "    $dumpfile(\"second.vcd\");\n"
                           "  end\n"
                           "endmodule\n"),
            "second.vcd");
}

TEST_F(DumpfileSysTask, OmittedArgumentDefaultsToDumpVcd) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial begin\n"
                           "    $dumpfile(\"other.vcd\");\n"
                           "    $dumpfile;\n"
                           "  end\n"
                           "endmodule\n"),
            "dump.vcd");
}

TEST_F(DumpfileSysTask, UnspecifiedFileNameWritesTheDefaultDumpVcd) {
  RunSource(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");

  EXPECT_EQ(NamesWritten(), "dump.vcd");
  EXPECT_NE(DumpFile("dump.vcd").find("$enddefinitions"), std::string::npos);
}

}  // namespace
