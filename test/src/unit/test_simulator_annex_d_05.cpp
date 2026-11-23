#include <gtest/gtest.h>

#include "helpers_annex_d_call_forms.h"

namespace {

constexpr const char* kKeyForm =
    "$key is written as a task statement with no argument or with one string "
    "naming the key file, and this call is not";

constexpr const char* kNokeyForm =
    "$nokey is written as a task statement with no argument, and this call is "
    "not";

TEST(KeyTaskForm, DISABLED_NokeyWithAnArgumentIsReported) {
  ExpectOnlyTheMalformedCallReported("$nokey", "$nokey(\"f.txt\")", kNokeyForm,
                                     "D.5");
}

TEST(KeyTaskForm, DISABLED_KeyWithTwoArgumentsIsReported) {
  ExpectOnlyTheMalformedCallReported(
      "$key(\"f.txt\")", "$key(\"a.txt\", \"b.txt\")", kKeyForm, "D.5");
}

TEST(KeyTaskForm, DISABLED_KeyWithAnEmptyArgumentListIsReported) {
  ExpectOnlyTheMalformedCallReported("$key(\"f.txt\")", "$key()", kKeyForm,
                                     "D.5");
}

TEST(KeyTaskForm, DISABLED_KeyWhoseArgumentIsNoStringIsReported) {
  ExpectOnlyTheMalformedCallReported("$key(\"f.txt\")", "$key(5)", kKeyForm,
                                     "D.5");
}

TEST(KeyTaskForm, DISABLED_KeyAndNokeyUsedAsFunctionsAreReported) {
  ExpectOnlyTheMalformedCallReported("$key", "v = $key", kKeyForm, "D.5");
  ExpectOnlyTheMalformedCallReported("$nokey", "v = $nokey", kNokeyForm, "D.5");
}

}  // namespace
