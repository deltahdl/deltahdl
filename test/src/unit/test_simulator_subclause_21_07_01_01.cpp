#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.7.1.1: run a module through parse, elaboration, lowering, and simulation,
// then report the VCD file name the $dumpfile call selected. Driving real
// source through the full pipeline is what lets each test observe the filename
// operand as it is actually produced -- a string literal, a string-typed
// variable, or an integral variable holding a character string -- rather than a
// hand-built value.
std::string RunAndDumpName(const std::string& src) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  if (design == nullptr) return "<elaboration-failed>";
  LowerAndRun(design, f);
  return f.ctx.GetDumpFileName();
}

// §21.7.1.1: the task specifies the name of the VCD file. The LRM's own example
// passes a string literal (§5.9), the simplest filename form.
TEST(DumpfileSysTask, StringLiteralSpecifiesFileName) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial $dumpfile(\"module1.dump\");\n"
                           "endmodule\n"),
            "module1.dump");
}

// §21.7.1.1: the filename may be a value of the string data type (§6.16), not
// only a literal. The variable is declared and assigned in source so the value
// reaches $dumpfile the way a real design would produce it.
TEST(DumpfileSysTask, StringVariableSpecifiesFileName) {
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
TEST(DumpfileSysTask, IntegralValueSpecifiesFileName) {
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
TEST(DumpfileSysTask, LaterCallReSpecifiesFileName) {
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
TEST(DumpfileSysTask, OmittedArgumentDefaultsToDumpVcd) {
  EXPECT_EQ(RunAndDumpName("module t;\n"
                           "  initial begin\n"
                           "    $dumpfile(\"other.vcd\");\n"
                           "    $dumpfile;\n"
                           "  end\n"
                           "endmodule\n"),
            "dump.vcd");
}

}  // namespace
