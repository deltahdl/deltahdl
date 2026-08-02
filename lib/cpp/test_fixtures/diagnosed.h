#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

// Whether a source was rejected, and whether the case that handed it over ever
// asked.
//
// A case asserts about what it names, and what it does not name is where this
// goes wrong. A source the tool rejected produces the same absences a rule
// under test produces -- no instance, no binding, no second diagnostic -- so a
// case asserting that something does not appear holds whether its rule works,
// works backwards, or was never written. Such a case is reported as passing
// for as long as it stands, and it is the case covering the rule.
//
// Reading discharges the obligation, whatever the case concludes from it: a
// case that has looked at the diagnostics has taken them into account. Never
// looking, on a source that was rejected, is the case that passed because its
// input never happened. The destructor reports that, because the end of the
// fixture's life is the last moment anybody could still have asked.
class Diagnosed {
 public:
  Diagnosed() = default;

  // A move carries the obligation to the new object and discharges it on the
  // old one, so a fixture returned by value is reported once, from whichever
  // object the case is left holding. Copying and assigning a whole obligation
  // have no caller and would each need an answer to that same question.
  Diagnosed(Diagnosed&& other) noexcept
      : errors_(other.errors_),
        asked_(other.asked_),
        source_(std::move(other.source_)) {
    other.asked_ = true;
  }
  Diagnosed(const Diagnosed&) = delete;
  Diagnosed& operator=(const Diagnosed&) = delete;
  Diagnosed& operator=(Diagnosed&&) = delete;

  // Records the outcome of compiling `source`, which the report quotes so that
  // the failure names the input rather than the harness.
  void Record(bool errors, std::string_view source) {
    errors_ = errors;
    asked_ = false;
    source_ = source;
  }

  // The same, for a caller that compiled the source itself and has only the
  // answer to hand.
  Diagnosed& operator=(bool errors) {
    errors_ = errors;
    asked_ = false;
    source_.clear();
    return *this;
  }

  // Asking. Every shape a case reads this in -- EXPECT_TRUE, EXPECT_FALSE, an
  // `if`, a `!`, a `||` -- arrives here, which is why the obligation is
  // discharged here rather than at any one of them.
  operator bool() const {
    asked_ = true;
    return errors_;
  }

  ~Diagnosed() {
    if (!errors_ || asked_) return;
    ADD_FAILURE() << "the source was rejected and the case never read the "
                     "diagnostics, so whatever it asserted was absent was "
                     "absent because nothing was compiled:\n"
                  << source_;
  }

 private:
  bool errors_ = false;
  mutable bool asked_ = false;
  std::string source_;
};
