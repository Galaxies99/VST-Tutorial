# VST-Tutorial

This is an VST Tutorial written by <a href = "https://github.com/QinxiangCao" >Qinxiang Cao</a> @ SJTU, first published at <a href = "https://bitbucket.org/qinxiang-SJTU/vst-tutorial/">BitBucket</a>.

The file `Tutorial.v` have a detailed introduction about <a href="https://github.com/PrincetonUniversity/VST">VST Tools</a>, which is a powerful tool made by Princeton University to help verify C program's correctness.

The file `Exercise.v` has some simple exercises about VST. All exercises are finished.

- Q: How to build this project?
- A: Following the steps below:
  - Clone VST from <a href=" https://github.com/PrincetonUniversity/VST ">Github</a>, clone this project, and place them in the same folder;
  - Compile VST (You may have to install Cygwin or some Linux-based command line tools if you are a Windows user).
  - Compile VST-Tutorial. Use commands (Linux):
    - `make depend`
    - `make all`
    - `make _CoqProject`
  - Open `Tutorial.v` or `Exercise.v`, then you can successfully compile them in Coq.

Last Updated on Feb. 23th, 2020.