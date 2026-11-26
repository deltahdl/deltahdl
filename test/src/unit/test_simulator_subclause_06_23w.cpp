#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(MailboxOfTypeReferenceSim, CarriesAByte) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  mailbox #(type(byte)) m = new;\n"
                       "  byte b;\n"
                       "  initial begin\n"
                       "    m.put(8'd200);\n"
                       "    m.get(b);\n"
                       "    $display(\"%0d\", b);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-56\n");
}

TEST(MailboxOfTypeReferenceSim, WeakReferenceOfAHandlesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class K; int m = 5; endclass\n"
                       "module top;\n"
                       "  K k;\n"
                       "  weak_reference #(type(k)) w;\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    w = new(k);\n"
                       "    $display(\"%0d\", w.get().m);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5\n");
}

}  // namespace
