FROM ltchentw/agda:latest

ENV HOME=/home
ENV AGDA_DIR=$HOME/.agda
ENV AGDA_LIBS=$AGDA_DIR/libraries

# Set up Agda configuration directories
RUN mkdir -p $AGDA_DIR && touch $AGDA_LIBS

WORKDIR $HOME

RUN apk update && apk upgrade && apk add --update alpine-sdk && \
    apk add --no-cache bash git openssh make cmake

# Install Cubical
RUN git clone https://github.com/agda/cubical --branch master
WORKDIR $HOME/cubical
RUN git checkout 581748b01bc43a25295993347bdc8c7cb2166090
RUN echo "$HOME/cubical/cubical.agda-lib" >> $AGDA_LIBS

WORKDIR $HOME

# Install Cubical Categorical Logic
RUN git clone https://github.com/maxsnew/cubical-categorical-logic --branch main
WORKDIR $HOME/cubical-categorical-logic
RUN git checkout 4e7b1c3a2ba7ed528b3cd9a4c3a5e7be3ff3449d
RUN echo "$HOME/cubical-categorical-logic/cubical-categorical-logic.agda-lib" >> $AGDA_LIBS

COPY . $HOME/dependent-lambek-calculus

WORKDIR /home/$USER_NAME/dependent-lambek-calculus

# Default command
CMD ["/bin/bash"]
