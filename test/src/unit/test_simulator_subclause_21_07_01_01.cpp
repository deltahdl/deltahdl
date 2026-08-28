#include <string>

#include "fixture_vcd_dump_from_source.h"

using namespace delta;

namespace {

// §21.7.1.1: run a module through parse, elaboration, lowering, and simulation,
// then report the VCD file name the $dumpfile call selected. Driving real
// source through the full pipeline is what lets each test observe the filename
// operand as it is actually produced -- a string literal, a string-typed
// variable, or an integral variable holding a character string -- rather than a
// hand-built value.
//
// The run stands in a scratch directory the fixture removes afterwards. The
// names below are relative, so a $dumpfile that goes on to open the file it
// named opens it wherever the process stands, and a test tree that ran these
// in the build directory would accumulate a module1.dump, a wave.vcd and a
// dump.vcd there.
class DumpfileSysTask : public VcdDumpFromSourceTestBase {
 protected:
  // The name the run's last $dumpfile selected, which is the name the task
  // records whether or not anything has yet opened a file under it.
  std::string RunAndDumpName(const std::string& src) {
    RunSource(src);
    return f_.ctx.GetDumpFileName();
  }
};

// §21.7.1.1: the task specifies the name of the VCD file. The LRM's own example
// passes a string literal (§5.9), the simplest filename form.
TEST_F(DumpfileSysTask, StringLiteralSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial $dumpfile(\"module1.dump\");\n"
                           "endmodule\n"),
            "module1.dump");
}

// §21.7.1.1: the filename may be a value of the string data type (§6.16), not
// only a literal. The variable is declared and assigned in source so the value
// reaches $dumpfile the way a real design would produce it.
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

// §21.7.1.1: an integral value whose bytes hold a character string also names
// the file. Assigning the string literal "wave" to a 32-bit reg packs its four
// characters into the word, which $dumpfile reads back as the file name.
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

// §21.7.1.1: each call specifies the name anew, so a later $dumpfile overrides
// the name an earlier one set.
TEST_F(DumpfileSysTask, LaterCallReSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial begin\n"
                           "    $dumpfile(\"first.vcd\");\n"
                           "    $dumpfile(\"second.vcd\");\n"
                           "  end\n"
                           "endmodule\n"),
            "second.vcd");
}

// §21.7.1.1: the filename argument is optional and defaults to "dump.vcd". A
// preceding call sets a different name first, so the bare call is observed to
// actively reset the name to the default rather than merely leaving it unset.
TEST_F(DumpfileSysTask, OmittedArgumentDefaultsToDumpVcd) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial begin\n"
                           "    $dumpfile(\"other.vcd\");\n"
                           "    $dumpfile;\n"
                           "  end\n"
                           "endmodule\n"),
            "dump.vcd");
}

// §21.7.1.1: "The filename is optional and defaults to the string literal
// "dump.vcd" if not specified." The cases above read the name back out of the
// run; this one reads the file the name produced, which is the only place the
// default can be observed to have been used for anything. §21.7.1.2 makes
// $dumpvars dump into the file specified by $dumpfile, so a source that calls
// $dumpvars and never calls $dumpfile at all specifies no name and dumps into
// the default one. $enddefinitions says the file went through the header and
// variable definitions of §21.7.2.1 rather than being an empty file the run
// touched, and the directory holding nothing else says the default name is
// the one that was used.
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
