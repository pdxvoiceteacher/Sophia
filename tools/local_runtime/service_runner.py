import subprocess
import sys


def main():
    subprocess.Popen(
        [
            sys.executable,
            "-m",
            "coherence.api.server",
        ]
    )

    print("[Sophia] Local API started on 4173")

    input("Press ENTER to exit\n")


if __name__ == "__main__":
    main()
