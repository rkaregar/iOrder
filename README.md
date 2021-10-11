# [Discovering Domain Orders via Order Dependencies]

This repository explains detailed steps on how to obtain domain orders via order dependencies.
This is based on the following paper:

**Discovering Domain Orders through Order Dependencies.**

Reza Karegar, Melicaalsadat Mirsafian, Parke Godfrey, Lukasz Golab, Mehdi Kargar, Divesh Srivastava, and Jaroslaw Szlichta

https://arxiv.org/abs/2005.14068

## 1. Compile the code

Go to `src/od` folder and run the following command. Note that required libraries are already in the lib forlder 

```
javac -d ../../out -cp .:../../lib/* *.java */*.java */*/*.java */*/*/*.java
```

## 2. Set up the config file

Ensure you fill up the `config.txt` file properly. This file is located in `/out` folder.

## 3. Run the code

Go to `out` folder and run the following command.

```
java -cp .:../lib/* od.MainClass
```

## 4. Obtain the results

The output of the algorithm will be printed in the standard output stream and 
aggregated results will be stored under the `stats/` folder.

