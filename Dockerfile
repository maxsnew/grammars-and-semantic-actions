FROM stvnschfr/cubical-categorical-logic:v1.0

RUN apt-get install make

COPY . $HOME/dependent-lambek-calculus

WORKDIR /home/$USER_NAME/dependent-lambek-calculus

RUN make gen-and-check-everythings

# Default command
CMD ["/bin/bash"]
