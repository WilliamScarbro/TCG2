# Updated TCG library

## Requirements
* ghc 9.2.7
* cabal 3.6.2.0

## Installation

Follow these steps to install `ghcup` and set up GHC 9.2.7 and Cabal 3.6.2.0 on Linux:

1. **Install GHCup** \
  Download and install `ghcup` using the following command:

   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
   ```

2. **Configure GHCup** \
   Ensure the ghcup binary is added to your PATH. Add the following line to your shell configuration file (e.g., .bashrc, .zshrc):
   ```
   export PATH="$HOME/.ghcup/bin:$PATH"
   ```
   Reload the shell configuration:
   ```
   source ~/.bashrc
   ```
3. **Install GHC 9.2.7** \
   Use ghcup to install the specified version of GHC:
   ```
   ghcup install ghc 9.2.7
   ```
   Set it as the default version:
   ```
   ghcup set ghc 9.2.7
   ```
4. **Install Cabal 3.6.2.0** \
   Use ghcup to install the specified version of Cabal:
   ```
   ghcup install cabal 3.6.2.0
   ```
   Set it as the default version:
   ```
   ghcup set cabal 3.6.2.0
   ```
   
5. **Verify Installation** \
   Confirm the installed versions of GHC and Cabal:
   ```
   ghc --version
   cabal --version
   ```
   You should see:
   ```
   The Glorious Glasgow Haskell Compilation System, version 9.2.7
   cabal-install version 3.6.2.0
   ```

## Usage

1. Start REPL
   ```
   cabal repl
   ```
   
2. Use `display_morph` to see imperative representation of algorithms

* simple algorithm
  ```
  display_morph (Base 4 0 4 5) (Factor 2)
  ```

* Spiral 4 step decomposition
  ```
  display_morph (Base 16 0 16 257) (spiral_4_step 16 8)
  ```

* Coopersmith's algorithm
  ```
  display_morph (Base 16 0 16 257) (qqft 4)
  ```

