/* Lean worker ABI. Native and wasm64 use the same generated Lean C. */
#include <lean/lean.h>
#include <stdint.h>
_Static_assert(sizeof(void*) == 8, "This worker requires a 64-bit Lean runtime (wasm64 in browsers)");
extern lean_object *initialize_LcalcVolunteer_Core(uint8_t builtin);
extern lean_object *lcalc_volunteer_compute(lean_object *input);
static int initialized = 0;
static lean_object *last_result = NULL;
LEAN_EXPORT int lcalc_worker_init(void) {
    if (initialized) return 0;
    lean_object *result = initialize_LcalcVolunteer_Core(1);
    if (!lean_io_result_is_ok(result)) { lean_dec(result); return 1; }
    lean_dec(result);
    lean_io_mark_end_initialization();
    lean_init_task_manager();
    initialized = 1;
    return 0;
}
LEAN_EXPORT const char *lcalc_worker_compute(const char *input) {
    if (lcalc_worker_init()) return "{\"status\":\"initialization-failed\"}";
    if (last_result) lean_dec(last_result);
    last_result = lcalc_volunteer_compute(lean_mk_string(input));
    return lean_string_cstr(last_result);
}
#ifdef LCALC_NATIVE_BRIDGE_TEST
extern int puts(const char *);
int main(int argc, char **argv) { if(argc != 2) return 2; puts(lcalc_worker_compute(argv[1])); return 0; }
#endif
