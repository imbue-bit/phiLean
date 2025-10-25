#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <poll.h>
#include <errno.h>

#define LEAN_EXECUTABLE "lean"
#define PROMPT "phiLean> "
#define BUFFER_SIZE 4096

pid_t start_lean_process(int *infd, int *outfd) {
    int stdin_pipe[2], stdout_pipe[2];

    if (pipe(stdin_pipe) < 0 || pipe(stdout_pipe) < 0) {
        perror("pipe failed");
        return -1;
    }

    pid_t pid = fork();
    if (pid < 0) {
        perror("fork failed");
        return -1;
    }

    if (pid == 0) {
        dup2(stdin_pipe[0], STDIN_FILENO);
        dup2(stdout_pipe[1], STDOUT_FILENO);
        dup2(stdout_pipe[1], STDERR_FILENO);

        close(stdin_pipe[0]);
        close(stdin_pipe[1]);
        close(stdout_pipe[0]);
        close(stdout_pipe[1]);

        execlp(LEAN_EXECUTABLE, LEAN_EXECUTABLE, NULL);
        perror("execlp failed");
        exit(1);
    }

    close(stdin_pipe[0]);
    close(stdout_pipe[1]);

    *infd = stdout_pipe[0];
    *outfd = stdin_pipe[1];

    return pid;
}

void read_from_lean(int lean_infd) {
    char buffer[BUFFER_SIZE];
    struct pollfd fds[1];
    fds[0].fd = lean_infd;
    fds[0].events = POLLIN;

    while (poll(fds, 1, 100) > 0) {
        if (fds[0].revents & POLLIN) {
            ssize_t bytes_read = read(lean_infd, buffer, BUFFER_SIZE - 1);
            if (bytes_read > 0) {
                buffer[bytes_read] = '\0';
                printf("%s", buffer);
                fflush(stdout);
            } else {
                break;
            }
        }
    }
}

int main() {
    int lean_infd, lean_outfd;
    pid_t lean_pid;

    lean_pid = start_lean_process(&lean_infd, &lean_outfd);
    if (lean_pid < 0) {
        fprintf(stderr, "Failed to start lean process. Is 'lean' in your PATH?\n");
        return 1;
    }

    sleep(1);
    read_from_lean(lean_infd);

    const char *import_cmd = "import Philib.Problems.Trolley\nimport Philib.Problems.Gettier\nimport Philib.Problems.ShipOfTheseus\n";
    if (write(lean_outfd, import_cmd, strlen(import_cmd)) < 0) {
        perror("write to lean failed");
    }
    read_from_lean(lean_infd);
    printf("philib environment loaded.\n");

    char *line = NULL;
    size_t len = 0;

    while (1) {
        printf(PROMPT);
        fflush(stdout);
        
        ssize_t line_len = getline(&line, &len, stdin);
        
        if (line_len == -1) { // EOF (Ctrl+D)
            printf("\nExiting phiLean.\n");
            break;
        }

        if (write(lean_outfd, line, line_len) < 0) {
            perror("write to lean failed");
            break;
        }

        read_from_lean(lean_infd);
    }

    free(line);
    close(lean_infd);
    close(lean_outfd);
    kill(lean_pid, SIGTERM);
    waitpid(lean_pid, NULL, 0);

    return 0;
}
