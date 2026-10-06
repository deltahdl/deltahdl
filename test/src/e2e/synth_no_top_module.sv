// A source that declares a type but no module gives synthesis nothing to lower,
// so the run says so and exits 1 rather than failing without a word.
typedef int t;
