to run fuzzing:

    cargo fuzz run read --sanitizer none -- -timeout=1 -max_len=32768