#pragma once

#include <string_view>

namespace delta {

// Whether `name` is a built-in system function, every one the standard defines
// listed by the clause defining it: §14.14, §16.14.7, §18.13, §19.9, and the
// functions of §20.3 to §20.15, §21.3 and §21.6. $cast (§8.16), $system
// (§20.17.1) and $stacktrace (§20.17.2) may each be called as a task or a
// function, and a statement calling one calls the task.
//
// The question has two askers, which is why it is not answered inside either.
// The VPI model builds a call of one as a vpiSysFuncCall rather than a
// vpiSysTaskCall (§37.42), and the elaborator gives §13.4.1's warning where
// one is called as if it had no return value: as a statement, or attached to a
// sequence (§16.11), which receives nothing back from it.
bool IsStandardSystemFunction(std::string_view name);

}  // namespace delta
