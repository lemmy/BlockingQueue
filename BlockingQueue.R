#library(ggplot2)
library(dplyr)
library(plotly)

data <- read.csv(header=TRUE, sep = "#", file = "output.csv") #file.choose())

summary = summarise(group_by(data,P,C,B,F,Level),
  # sd_WaitSet = sd(WaitSet),
  # sd_EP = sd(EP),
  # sd_EC = sd(EC),
  # sd_Lock = sd(lock),
  # sd_Worked = sd(worked),
  WaitSet = ceiling(mean(WaitSet)),
  Busy = ceiling(mean(Busy)),
  #EP = mean(EP),
  #EC = mean(EC),a
  #lock = mean(lock),
  worked = mean(worked)
)

fig <- plot_ly(data = filter(data, Level==max(data$Level)),
               x = ~C,
               y = ~B,
               z = ~worked,
               name = "Throuhgput"
)
fig

# ## Throughput
# p2 <- plot_ly(summary, y = ~worked, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
#   add_markers()
# p2
# ## Waitset
# p3 <- plot_ly(summary, y = ~WaitSet, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
#   add_markers()
# p3
# 
# subplot(p2, p3, nrows = 2, titleX = TRUE, titleY = TRUE)

###

configs <- distinct(summary[1:3])

plts <- list()

for (conf in 1:nrow(configs)) {
  p <- configs[conf,"P"]
  c <- configs[conf,"C"]
  b <- configs[conf,"B"]
  df <- filter(summary, P==p, C==c, B==b)
  ## Throughput
  p1 <- plot_ly(df, y = ~worked, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
    add_markers() %>% layout(yaxis=list(title=paste("P/C/B", p, c, b)))
  plts <- append(plts, list(p1))
  ## Busy
  p2 <- plot_ly(df, y = ~Busy, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
    add_markers()
  plts <- append(plts, list(p2))
  ## Waitset
  p3 <- plot_ly(df, y = ~WaitSet, x = ~Level, color=~F, type = 'scatter', mode = 'lines') %>%
    add_markers()
  plts <- append(plts, list(p3))
  
   # plts <- append(plts, list(subplot(p2, p3)))
#  plts <- append(plts, list(p2))
}

subplot(plts, nrows = nrow(configs), titleY = TRUE, titleX = FALSE)

