FROM stvnschfr/cubical-categorical-logic:v1.0

RUN apt-get install make

COPY . $HOME/grammars-and-semantic-actions/code/Cubical

WORKDIR /home/$USER_NAME/grammars-and-semantic-actions/code/Cubical

RUN make gen-and-check-everythings

# Default command
CMD ["/bin/bash"]
