SDK: temurin-11 (Eclipse Temurin version 11.0.17)
Language Level: SDK default(11 - Local variable syntax for lambda parameters)

The project consists of 6 packages in a Sources Root. 
In order to run the game in offline version, please refer to running OthelloTUI class in GameLogic package. 

In terms of playing Othello game agains other players, you have to: 
1. Run the ServerMain class in Networking package (port 2020)
2. Run multiple instances of Client class in Client package. This can be done by using IntelliJ, go to Run -> Edit Configurations -> Add new run configuration -> Application -> Click to Main class in "Build and run" -> choose the Client class -> OK. On the main page when having pressed OK, choose Modify options -> In Operating System, choose Allow Multiple Instances.
