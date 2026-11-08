#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MailboxPutElaborator, PutCallElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxPutElaborator, PutWithObjectHandleArg) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  mailbox mb;\n"
      "  C obj = new;\n"
      "  initial begin\n"
      "    mb.put(obj);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxPutElaborator, PutOfAnUnpackedArrayIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new;\n"
      "  int arr[2];\n"
      "  initial mb.put(arr);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "message of mailbox method 'put' is of an unpacked aggregate type", 4,
      "15.4.3"));
}

TEST(MailboxPutElaborator, PutOfAPackedStructOrAHandleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class C; endclass\n"
      "  typedef struct packed { int x; } ps_t;\n"
      "  mailbox mb = new;\n"
      "  ps_t p;\n"
      "  C h;\n"
      "  initial begin\n"
      "    mb.put(p);\n"
      "    mb.put(h);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
